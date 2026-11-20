-- Prove2me | solution 1 for P010.orderedPrimeClass_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:48:08.715711+00:00
-- url     : https://prove2.me/submissions/e1018f66-63d0-4143-b5c5-814ee55d6ce8

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_orderedPrimeClass_toFinset
public import Theorems.Thm_P010_orderedPrimeClass_nodup
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
theorem _root_.solution (n p u v : ℕ)
    (hu : u ∈ primeClass n p) (hv : v ∈ primeClass n p)
    (huv : u ≠ v) :
    (orderedPrimeClass n p u v).Perm (primeClass n p).toList := by
  classical
  apply List.perm_of_nodup_nodup_toFinset_eq
    (orderedPrimeClass_nodup n p u v huv)
    (Finset.nodup_toList _)
  simpa using orderedPrimeClass_toFinset n p u v hu hv
end P010
