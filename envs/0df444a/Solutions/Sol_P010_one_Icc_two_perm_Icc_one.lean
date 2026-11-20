-- Prove2me | solution 1 for P010.one_Icc_two_perm_Icc_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:53:20.797057+00:00
-- url     : https://prove2.me/submissions/3b0c44f3-9f97-494f-b847-5c59a56205f2

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
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
theorem _root_.solution (n : ℕ) (hn : 1 ≤ n) :
    (1 :: (Finset.Icc 2 n).toList).Perm
      (Finset.Icc 1 n).toList := by
  classical
  apply List.perm_of_nodup_nodup_toFinset_eq
    (by simp [Finset.nodup_toList]) (Finset.nodup_toList _)
  ext x
  simp only [List.toFinset_cons, Finset.toList_toFinset,
    Finset.mem_insert, Finset.mem_Icc]
  omega
end P010
