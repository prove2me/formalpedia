-- Prove2me | solution 1 for P010.classConcat_all_primes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:51:43.130176+00:00
-- url     : https://prove2.me/submissions/51932c03-6a67-4769-9412-d76083285339

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_primeClass_partition
public import Theorems.Thm_P010_classConcat_nodup
public import Theorems.Thm_P010_classConcat_toFinset
public import Theorems.Thm_Nat_Prime_maxPrimeFac_eq_self
public import Theorems.Thm_Nat_maxPrimeFac_eq_self_iff
public import Theorems.Thm_Nat_maxPrimeFac_one
public import Theorems.Thm_Nat_maxPrimeFac_pow
public import Theorems.Thm_Nat_maxPrimeFac_zero
public import Theorems.Thm_Nat_one_le_maxPrimeFac_iff
public import Theorems.Thm_Nat_one_lt_maxPrimeFac_iff
attribute [local simp] Nat.Prime.maxPrimeFac_eq_self
attribute [local simp] Nat.maxPrimeFac_eq_self_iff
attribute [local simp] Nat.maxPrimeFac_one
attribute [local simp] Nat.maxPrimeFac_pow
attribute [local simp] Nat.maxPrimeFac_zero
attribute [local simp] Nat.one_le_maxPrimeFac_iff
attribute [local simp] Nat.one_lt_maxPrimeFac_iff



set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n : ℕ) :
    (classConcat n n.primesLE.toList).Perm
      (Finset.Icc 2 n).toList := by
  classical
  apply List.perm_of_nodup_nodup_toFinset_eq
    (classConcat_nodup n _ (Finset.nodup_toList _))
    (Finset.nodup_toList _)
  simpa only [classConcat_toFinset, Finset.toList_toFinset] using
    primeClass_partition n
end P010
