#![cfg_attr(not(feature = "std"), no_std)]


pub use self::multisig::{ConfirmationStatus, Multisig, Transaction};

use ink_lang as ink;

#[ink::contract]
mod multisig {
    use ink_env::{
        call::{build_call, utils::ReturnType, CallParam, ExecutionInput, Selector}, 
        test::Calldata,
    };

    use ink_prelude::vec::Vec;
    use ink_storage::{
        collections::{HashMap as StorageHashMap, Stash as StorageStash, Vec as StorageVec},
        traits::{PackedLayout, SpreadLayout},
        Lazy,
    };
    use scale::Output;
    
    

    const MAX_OWNERS: u32 = 50;

    type TransactionId = u32;

    const WRONG_TRANSACTION_ID: &str = "The user specified an invalid transaction id. Abort.";

    struct CallInput<'a>(&'a [u8]);

    impl<'a> scale::Encode for CallInput<'a> {
        fn encode_to<T: Output>(&self, dest: &mut T) {
            dest.write(self.0);
        }
    }

    #[derive(scale::Encode, scale::Decode, Clone, Copy, SpreadLayout, PackedLayout)]
    #[cfg_attr(
        feature = "std",
        derive(scale_info::TypeInfo, ink_storage::traits::StorageLayout)
    )]
    pub enum ConfirmationStatus {
        Confirmed,
        ConfirmationsNeeded(u32),
    }

    #[derive(scale::Encode, scale::Decode, SpreadLayout, PackedLayout)]
    #[cfg_attr(
        feature = "std",
        derive(
            Debug,
            PartialEq,
            Eq,
            scale_info::TypeInfo,
            ink_storage::traits::StorageLayout
        )
    )]
    pub struct Transaction {
        pub callee: AccountId,
        pub selector: [u8; 4],
        pub input: Vec<u8>,
        pub transferred_value: Balance,
        pub gas_limit: u64,
    }

    #[derive(Copy, Clone, Debug, PartialEq, Eq, scale::Encode, scale::Decode)]
    #[cfg_attr(feature = "std", derive(::scale_info::TypeInfo))]
    pub enum Error {
        TransactionFailed,
    }

    #[ink(storage)]
    pub struct Multisig {
        confirmations: StorageHashMap<(TransactionId, AccountId), ()>,
        confirmation_count: StorageHashMap<TransactionId, u32>,
        transactions: StorageStash<Transaction>,
        owners: StorageVec<AccountId>,
        is_owner: StorageHashMap<AccountId, ()>,
        wallet_id: StorageHashMap<AccountId, ()>,
        requirement: Lazy<u32>,
    }

    #[ink(event)]
    pub struct Confirmation {
        #[ink(topic)]
        transaction: TransactionId,
        #[ink(topic)]
        from: AccountId,
        #[ink(topic)]
        status: ConfirmationStatus,
    }

    #[ink(event)]
    pub struct Revokation {
        #[ink(topic)]
        transaction: TransactionId,
        #[ink(topic)]
        from: AccountId,
    }

    #[ink(event)]
    pub struct Submission {
        #[ink(topic)]
        transaction: TransactionId,
    }

    #[ink(event)]
    pub struct Cancelation {
        #[ink(topic)]
        transaction: TransactionId,
    }

    #[ink(event)]
    pub struct Execution {
        #[ink(topic)]
        transaction: TransactionId,

        #[ink(topic)]
        result: Result<Option<Vec<u8>>, Error>,
    }

    #[ink(event)]
    pub struct OwnerAddition {
        #[ink(topic)]
        owner: AccountId,
    }

    #[ink(event)]
    pub struct OwnerRemoval {
        #[ink(topic)]
        owner: AccountId,
    }

    #[ink(event)]
    pub struct RequirementChange {
        new_requirement: u32,
    }

    impl Multisig {
        #[ink(constructor)]
        pub fn new(requirement: u32, owners: Vec<AccountId>) -> Self {
            let is_owner: StorageHashMap<_, _, _> =
                owners.iter().copied().map(|owner| (owner, ())).collect();
            let owners: StorageVec<_> = owners.iter().copied().collect();
            let wallet_id: AccountId = [7u8; 32].into();
            ensure_requirement_is_valid(owners.len(), requirement);
            assert!(is_owner.len() == owners.len());
            Self {
                confirmations: StorageHashMap::default(),
                confirmation_count: StorageHashMap::default(),
                transactions: StorageStash::default(),
                owners,
                is_owner,
                wallet_id,
                requirement: Lazy::new(requirement),
            }
        }

        #[ink(message)]
        pub fn add_owner(&mut self, new_owner: AccountId) {
            self.ensure_from_wallet();
            self.ensure_no_owner(&new_owner);
            ensure_requirement_is_valid(self.owners.len() + 1, *self.requirement);
            self.is_owner.insert(new_owner, ());
            self.owners.push(new_owner);
            self.env().emit_event(OwnerAddition { owner: new_owner });
            let alice: AccountId = [1u8; 32].into();
            let mut call = CallData::new(Selector::new([166, 229, 27, 154])); // add_owner
            call.push_arg(&alice);
            let transaction = Transaction {
                callee: wallet_id,
                selector: call.selector().to_bytes(),
                input: call.params().to_owned(),
                transferred_value: 1,
                gas_limit: 100
            };
            let mut submit = CallParams::<Env, _, _>::eval(
                wallet_id,
                Selector::new([86, 244, 13, 223]) 
                );
            let (id, _): (u32, ConfirmationStatus)  = submit.push_arg(&transaction)
                .fire()
                .expect("submit_transaction won't panic");
            let mut invoke = CallParams::<Env, _, ()>::invoke(
                wallet_id, 
                Selector::new([185, 50, 225, 236]) // invoke_transaction 
                );
            invoke.push_arg(&id).fire();
            
            



        }

        #[ink(message)]
        pub fn remove_owner(&mut self, owner: AccountId) {
            self.ensure_from_wallet();
            self.ensure_owner(&owner);
            let len = self.owners.len() - 1;
            let requirement = u32::min(len, *self.requirement);
            ensure_requirement_is_valid(len, requirement);
            self.owners.swap_remove(self.owner_index(&owner));
            self.is_owner.take(&owner);
            Lazy::set(&mut self.requirement, requirement);
            self.clean_owner_confirmations(&owner);
            self.env().emit_event(OwnerRemoval { owner });
        }

        #[ink(message)]
        pub fn replace_owner(&mut self, old_owner: AccountId, new_owner: AccountId) {
            self.ensure_from_wallet();
            self.ensure_owner(&old_owner);
            self.ensure_no_owner(&new_owner);
            let owner_index = self.owner_index(&old_owner);
            self.owners[owner_index] = new_owner;
            self.is_owner.take(&old_owner);
            self.is_owner.insert(new_owner, ());
            self.clean_owner_confirmations(&old_owner);
            self.env().emit_event(OwnerRemoval { owner: old_owner });
            self.env().emit_event(OwnerAddition { owner: new_owner });
        }

        #[ink(message)]
        pub fn change_requirement(&mut self, new_requirement: u32) {
            self.ensure_from_wallet();
            ensure_requirement_is_valid(self.owners.len(), new_requirement);
            Lazy::set(&mut self.requirement, new_requirement);
            self.env().emit_event(RequirementChange { new_requirement });
        }

        #[ink(message)]
        pub fn submit_transaction(
            &mut self,
            transaction: Transaction,
        ) -> (TransactionId, ConfirmationStatus) {
            self.ensure_caller_is_owner();
            let trans_id = self.transactions.put(transaction);
            self.env().emit_event(Submission {
                transaction: trans_id,
            });
            (
                trans_id,
                self.confirm_by_caller(self.env().caller(), trans_id),
            )
        }

        #[ink(message)]
        pub fn cancel_transaction(&mut self, trans_id: TransactionId) {
            self.ensure_from_wallet();
            if self.take_transaction(trans_id).is_some() {
                self.env().emit_event(Cancelation {
                    transaction: trans_id,
                });
            }
        }

        #[ink(message)]
        pub fn confirm_transaction(&mut self, trans_id: TransactionId) -> ConfirmationStatus {
            self.ensure_caller_is_owner();
            self.ensure_transaction_exists(trans_id);
            self.confirm_by_caller(self.env().caller(), trans_id)
        }

        #[ink(message)]
        pub fn revoke_confirmation(&mut self, trans_id: TransactionId) {
            self.ensure_caller_is_owner();
            let caller = self.env().caller();
            if self.confirmations.take(&(trans_id, caller)).is_some() {
                self.confirmation_count
                    .entry(trans_id)
                    .and_modify(|v| {
                        if *v > 0 {
                            *v -= 1;
                        }
                    })
                    .or_insert(1);
                self.env().emit_event(Revokation {
                    transaction: trans_id,
                    from: caller,
                });
            }
        }

        #[ink(message)]
        pub fn invoke_transaction(&mut self, trans_id: TransactionId) -> Result<(), Error> {
            self.ensure_confirmed(trans_id);
            let t = self.take_transaction(trans_id).expect(WRONG_TRANSACTION_ID);
            let result = build_call::<<Self as ::ink_lang::ContractEnv>::Env>()
                .callee(t.callee)
                .gas_limit(t.gas_limit)
                .transferred_value(t.transferred_value)
                .exec_input(ExecutionInput::new(t.selector.into()).push_arg(CallInput(&t.input)))
                .returns::<()>()
                .fire()
                .map_err(|_| Error::TransactionFailed);
            self.env().emit_event(Execution {
                transaction: trans_id,
                result: result.map(|_| None),
            });
            result
        }

        #[ink(message)]
        pub fn eval_transaction(&mut self, trans_id: TransactionId) -> Result<Vec<u8>, Error> {
            self.ensure_confirmed(trans_id);
            let t = self.take_transaction(trans_id).expect(WRONG_TRANSACTION_ID);
            let result = build_call::<<Self as ::ink_lang::ContractEnv>::Env>()
                .callee(t.callee)
                .gas_limit(t.gas_limit)
                .transferred_value(t.transferred_value)
                .exec_input(ExecutionInput::new(t.selector.into()).push_arg(CallInput(&t.input)))
                .returns::<ReturnType<Vec<u8>>>()
                .fire()
                .map_err(|_| Error::TransactionFailed);
            self.env().emit_event(Execution {
                transaction: trans_id,
                result: result.clone().map(Some),
            });
            result
        }

        fn confirm_by_caller(
            &mut self,
            confirmer: AccountId,
            transaction: TransactionId,
        ) -> ConfirmationStatus {
            let count = self.confirmation_count.entry(transaction).or_insert(0);
            let new_confirmation = self
                .confirmations
                .insert((transaction, confirmer), ())
                .is_none();
            if new_confirmation {
                *count += 1;
            }
            let status = {
                if *count >= *self.requirement {
                    ConfirmationStatus::Confirmed
                } else {
                    ConfirmationStatus::ConfirmationsNeeded(*self.requirement - *count)
                }
            };
            if new_confirmation {
                self.env().emit_event(Confirmation {
                    transaction,
                    from: confirmer,
                    status,
                });
            }
            status
        }

        fn owner_index(&self, owner: &AccountId) -> u32 {
            self.owners.iter().position(|x| *x == *owner).expect(
                "This is only called after it was already verified that the id is
                 actually an owner.",
            ) as u32
        }

        fn take_transaction(&mut self, trans_id: TransactionId) -> Option<Transaction> {
            let transaction = self.transactions.take(trans_id);
            if transaction.is_some() {
                self.clean_transaction_confirmations(trans_id);
            }
            transaction
        }

        fn clean_owner_confirmations(&mut self, owner: &AccountId) {
            use ::ink_storage::collections::stash::Entry as StashEntry;
            for (trans_id, _) in self
                .transactions
                .entries()
                .enumerate()
                .filter_map(|(n, entry)| match entry {
                    StashEntry::Vacant(_) => None,
                    StashEntry::Occupied(value) => Some((n as u32, value)),
                })
            {
                if self.confirmations.take(&(trans_id, *owner)).is_some() {
                    *self.confirmation_count.entry(trans_id).or_insert(0) += 1;
                }
            }
        }

        fn clean_transaction_confirmations(&mut self, transaction: TransactionId) {
            for owner in self.owners.iter() {
                self.confirmations.take(&(transaction, *owner));
            }
            self.confirmation_count.take(&transaction);
        }

        fn ensure_confirmed(&self, trans_id: TransactionId) {
            assert!(
                self.confirmation_count
                    .get(&trans_id)
                    .expect(WRONG_TRANSACTION_ID)
                    >= &self.requirement
            );
        }

        fn ensure_transaction_exists(&self, trans_id: TransactionId) {
            self.transactions.get(trans_id).expect(WRONG_TRANSACTION_ID);
        }

        fn ensure_caller_is_owner(&self) {
            self.ensure_owner(&self.env().caller());
        }

        fn ensure_from_wallet(&self) {
            assert_eq!(self.env().caller(), self.env().account_id());
        }

        fn ensure_owner(&self, owner: &AccountId) {
            assert!(self.is_owner.contains_key(owner));
        }

        fn ensure_no_owner(&self, owner: &AccountId) {
            assert!(!self.is_owner.contains_key(owner));
        }
    }
    fn ensure_requirement_is_valid(owners: u32, requirement: u32) {
        assert!(0 < requirement && requirement <= owners && owners <= MAX_OWNERS);
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use ink_env::{call, test};
        type Accounts = test::DefaultAccounts<Environment>;
        const WALLET: [u8; 32] = [7; 32];

        impl Transaction {
            fn change_requirement(requirement: u32) -> Self {
                let mut call = test::CallData::new(call::Selector::new([0x00; 4]));
                call.push_arg(&requirement);
                Self {
                    callee: WALLET.into(),
                    selector: call.selector().to_bytes(),
                    input: call.params().to_owned(),
                    transferred_value: 0,
                    gas_limit: 1000000,
                }
            }
        }

        fn set_sender(sender: AccountId) {
            test::push_execution_context::<Environment>(
                sender,
                WALLET.into(),
                1000000,
                1000000,
                test::CallData::new(call::Selector::new([0x00; 4])),
            );
        }

        fn set_from_wallet() {
            set_sender(WALLET.into());
        }

        fn set_from_owner() {
            let accounts = default_accounts();
            set_sender(accounts.alice);
        }

        fn set_from_noowner() {
            let accounts = default_accounts();
            set_sender(accounts.django);
        }

        fn default_accounts() -> Accounts {
            test::default_accounts().expect("Test environment is expected to be initialized.")
        }

        fn build_contract() -> Multisig {
            let accounts = default_accounts();
            let owners = ink_prelude::vec![accounts.alice, accounts.bob, accounts.eve];
            Multisig::new(2, owners)
        }

        fn submit_transaction() -> Multisig {
            let mut contract = build_contract();
            let accounts = default_accounts();
            set_from_owner();
            contract.submit_transaction(Transaction::change_requirement(1));
            assert_eq!(contract.transactions.len(), 1);
            assert_eq!(test::recorded_events().count(), 2);
            let transaction = contract.transactions.get(0).unwrap();
            assert_eq!(*transaction, Transaction::change_requirement(1));
            contract.confirmations.get(&(0, accounts.alice)).unwrap();
            assert_eq!(contract.confirmations.len(), 1);
            assert_eq!(*contract.confirmation_count.get(&0).unwrap(), 1);
            contract
        }

        #[test]
        fn construction_works() {
            let accounts = default_accounts();
            let owners = ink_prelude::vec![accounts.alice, accounts.bob, accounts.eve];
            let contract = build_contract();

            assert_eq!(contract.owners.len(), 3);
            assert_eq!(*contract.requirement, 2);
            assert!(contract.owners.iter().eq(owners.iter()));
            assert!(contract.is_owner.get(&accounts.alice).is_some());
            assert!(contract.is_owner.get(&accounts.bob).is_some());
            assert!(contract.is_owner.get(&accounts.eve).is_some());
            assert!(contract.is_owner.get(&accounts.charlie).is_none());
            assert!(contract.is_owner.get(&accounts.django).is_none());
            assert!(contract.is_owner.get(&accounts.frank).is_none());
            assert_eq!(contract.confirmations.len(), 0);
            assert_eq!(contract.confirmation_count.len(), 0);
            assert_eq!(contract.transactions.len(), 0);
        }

        #[test]
        #[should_panic]
        fn empty_owner_construction_fails() {
            Multisig::new(0, vec![]);
        }

        #[test]
        #[should_panic]
        fn zero_requirement_construction_fails() {
            let accounts = default_accounts();
            Multisig::new(0, vec![accounts.alice, accounts.bob]);
        }

        #[test]
        #[should_panic]
        fn too_large_requirement_construction_fails() {
            let accounts = default_accounts();
            Multisig::new(3, vec![accounts.alice, accounts.bob]);
        }

        #[test]
        fn add_owner_works() {
            let accounts = default_accounts();
            let mut contract = build_contract();
            set_from_wallet();
            let owners = contract.owners.len();
            contract.add_owner(accounts.frank);
            assert_eq!(contract.owners.len(), owners + 1);
            assert!(contract.is_owner.get(&accounts.frank).is_some());
            assert_eq!(test::recorded_events().count(), 1);
        }

        #[test]
        #[should_panic]
        fn add_existing_owner_fails() {
            let accounts = default_accounts();
            let mut contract = build_contract();
            set_from_wallet();
            contract.add_owner(accounts.bob);
        }

        #[test]
        #[should_panic]
        fn add_owner_permission_denied() {
            let accounts = default_accounts();
            let mut contract = build_contract();
            set_from_owner();
            contract.add_owner(accounts.frank);
        }

        #[test]
        fn remove_owner_works() {
            let accounts = default_accounts();
            let mut contract = build_contract();
            set_from_wallet();
            let owners = contract.owners.len();
            contract.remove_owner(accounts.alice);
            assert_eq!(contract.owners.len(), owners - 1);
            assert!(contract.is_owner.get(&accounts.alice).is_none());
            assert_eq!(test::recorded_events().count(), 1);
        }

        #[test]
        #[should_panic]
        fn remove_owner_nonexisting_fails() {
            let accounts = default_accounts();
            let mut contract = build_contract();
            set_from_wallet();
            contract.remove_owner(accounts.django);
        }

        #[test]
        #[should_panic]
        fn remove_owner_permission_denied() {
            let accounts = default_accounts();
            let mut contract = build_contract();
            set_from_owner();
            contract.remove_owner(accounts.alice);
        }

        #[test]
        fn replace_owner_works() {
            let accounts = default_accounts();
            let mut contract = build_contract();
            set_from_wallet();
            let owners = contract.owners.len();
            contract.replace_owner(accounts.alice, accounts.django);
            assert_eq!(contract.owners.len(), owners);
            assert!(contract.is_owner.get(&accounts.alice).is_none());
            assert!(contract.is_owner.get(&accounts.django).is_some());
            assert_eq!(test::recorded_events().count(), 2);
        }

        #[test]
        #[should_panic]
        fn replace_owner_existing_fails() {
            let accounts = default_accounts();
            let mut contract = build_contract();
            set_from_wallet();
            contract.replace_owner(accounts.alice, accounts.bob);
        }

        #[test]
        #[should_panic]
        fn replace_owner_nonexisting_fails() {
            let accounts = default_accounts();
            let mut contract = build_contract();
            set_from_wallet();
            contract.replace_owner(accounts.django, accounts.frank);
        }

        #[test]
        #[should_panic]
        fn replace_owner_permission_denied() {
            let accounts = default_accounts();
            let mut contract = build_contract();
            set_from_owner();
            contract.replace_owner(accounts.alice, accounts.django);
        }

        #[test]
        fn change_requirement_works() {
            let mut contract = build_contract();
            assert_eq!(*contract.requirement, 2);
            set_from_wallet();
            contract.change_requirement(3);
            assert_eq!(*contract.requirement, 3);
            assert_eq!(test::recorded_events().count(), 1);
        }

        #[test]
        #[should_panic]
        fn change_requirement_too_high() {
            let mut contract = build_contract();
            set_from_wallet();
            contract.change_requirement(4);
        }

        #[test]
        #[should_panic]
        fn change_requirement_zero_fails() {
            let mut contract = build_contract();
            set_from_wallet();
            contract.change_requirement(0);
        }

        #[test]
        fn submit_transaction_works() {
            submit_transaction();
        }

        #[test]
        #[should_panic]
        fn submit_transaction_noowner_fails() {
            let mut contract = build_contract();
            set_from_noowner();
            contract.submit_transaction(Transaction::change_requirement(1));
        }

        #[test]
        #[should_panic]
        fn submit_transaction_wallet_fails() {
            let mut contract = build_contract();
            set_from_wallet();
            contract.submit_transaction(Transaction::change_requirement(1));
        }

        #[test]
        fn cancel_transaction_works() {
            let mut contract = submit_transaction();
            set_from_wallet();
            contract.cancel_transaction(0);
            assert_eq!(contract.transactions.len(), 0);
            assert_eq!(test::recorded_events().count(), 3);
        }

        #[test]
        fn cancel_transaction_nonexisting() {
            let mut contract = submit_transaction();
            set_from_wallet();
            contract.cancel_transaction(1);
            assert_eq!(contract.transactions.len(), 1);
            assert_eq!(test::recorded_events().count(), 2);
        }

        #[test]
        #[should_panic]
        fn cancel_transaction_no_permission() {
            let mut contract = submit_transaction();
            contract.cancel_transaction(0);
        }

        #[test]
        fn confirm_transaction_works() {
            let mut contract = submit_transaction();
            let accounts = default_accounts();
            set_sender(accounts.bob);
            contract.confirm_transaction(0);
            assert_eq!(test::recorded_events().count(), 3);
            contract.confirmations.get(&(0, accounts.bob)).unwrap();
            assert_eq!(contract.confirmations.len(), 2);
            assert_eq!(*contract.confirmation_count.get(&0).unwrap(), 2);
        }

        #[test]
        fn revoke_confirmations() {
            let mut contract = submit_transaction();
            let accounts = default_accounts();
            set_sender(accounts.bob);
            contract.confirm_transaction(0);
            set_sender(accounts.eve);
            contract.confirm_transaction(0);
            assert_eq!(contract.confirmations.len(), 3);
            assert_eq!(*contract.confirmation_count.get(&0).unwrap(), 3);
            contract.revoke_confirmation(0);
            assert_eq!(*contract.confirmation_count.get(&0).unwrap(), 2);
            set_sender(accounts.bob);
            contract.revoke_confirmation(0);
            assert_eq!(*contract.confirmation_count.get(&0).unwrap(), 1);
        }

        #[test]
        fn confirm_transaction_already_confirmed() {
            let mut contract = submit_transaction();
            let accounts = default_accounts();
            set_sender(accounts.alice);
            contract.confirm_transaction(0);
            assert_eq!(test::recorded_events().count(), 2);
            contract.confirmations.get(&(0, accounts.alice)).unwrap();
            assert_eq!(contract.confirmations.len(), 1);
            assert_eq!(*contract.confirmation_count.get(&0).unwrap(), 1);
        }

        #[test]
        #[should_panic]
        fn confirm_transaction_noowner_fail() {
            let mut contract = submit_transaction();
            set_from_noowner();
            contract.confirm_transaction(0);
        }

        #[test]
        fn revoke_transaction_works() {
            let mut contract = submit_transaction();
            let accounts = default_accounts();
            set_sender(accounts.alice);
            contract.revoke_confirmation(0);
            assert_eq!(test::recorded_events().count(), 3);
            assert!(contract.confirmations.get(&(0, accounts.alice)).is_none());
            assert_eq!(contract.confirmations.len(), 0);
            assert_eq!(*contract.confirmation_count.get(&0).unwrap(), 0);
        }

        #[test]
        fn revoke_transaction_no_confirmer() {
            let mut contract = submit_transaction();
            let accounts = default_accounts();
            set_sender(accounts.bob);
            contract.revoke_confirmation(0);
            assert_eq!(test::recorded_events().count(), 2);
            assert!(contract.confirmations.get(&(0, accounts.alice)).is_some());
            assert_eq!(contract.confirmations.len(), 1);
            assert_eq!(*contract.confirmation_count.get(&0).unwrap(), 1);
        }

        #[test]
        #[should_panic]
        fn revoke_transaction_noowner_fail() {
            let mut contract = submit_transaction();
            let accounts = default_accounts();
            set_sender(accounts.django);
            contract.revoke_confirmation(0);
        }
    }
}
