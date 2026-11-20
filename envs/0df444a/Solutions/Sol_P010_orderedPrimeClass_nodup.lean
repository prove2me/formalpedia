-- Prove2me | solution 1 for P010.orderedPrimeClass_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:46:50.842699+00:00
-- url     : https://prove2.me/submissions/02220e4c-63d2-4cd5-bbc0-3414902eb0c6

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
theorem _root_.solution (n p u v : ℕ) (huv : u ≠ v) :
    (orderedPrimeClass n p u v).Nodup := by
  classical
  unfold orderedPrimeClass
  apply List.nodup_cons.mpr
  constructor
  · simp [Finset.mem_erase, huv]
  · apply List.nodup_append'.mpr
    refine ⟨Finset.nodup_toList _, by simp, ?_⟩
    intro m hm hv
    have hnot : m ≠ v :=
      (Finset.mem_erase.mp (Finset.mem_toList.mp hm)).1
    exact hnot (by simpa using hv)
end P010
