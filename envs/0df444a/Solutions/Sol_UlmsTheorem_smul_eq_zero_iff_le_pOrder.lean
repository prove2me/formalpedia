-- Prove2me | solution 1 for UlmsTheorem.smul_eq_zero_iff_le_pOrder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:55:53.478556+00:00
-- url     : https://prove2.me/submissions/62d9c70f-295c-4087-9796-f9d34324a6b4

module
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Heights
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.NormNum.GCD
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Pure
public import Theorems.Thm_UlmsTheorem_pOrder_zero
public import Theorems.Thm_UlmsTheorem_mem_pImage
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_add_one_iff
public import Theorems.Thm_UlmsTheorem_pHeight_zero
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_zero
attribute [local simp] UlmsTheorem.mem_pImage
attribute [local simp] UlmsTheorem.mem_ulmSubgroup_add_one_iff
attribute [local simp] UlmsTheorem.pHeight_zero
attribute [local simp] UlmsTheorem.ulmSubgroup_zero


attribute [local simp] UlmsTheorem.pOrder_zero

set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal
universe u
variable (p : ℕ)
variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]
namespace UlmsTheorem
theorem _root_.solution (x : G) (n : ℕ) :
    p ^ n • x = 0 ↔ pOrder p x ≤ n := by
  constructor
  · intro hx
    exact iInf_le_of_le n <| iInf_le_of_le hx le_rfl
  · intro h
    by_contra hx
    have hlt : (n : ℕ∞) < pOrder p x := by
      rw [pOrder]
      refine (lt_iInf_iff).2 ?_
      refine ⟨(n + 1 : ℕ∞), by
        simpa using (ENat.lt_natCast_add_one_iff (m := (n : ℕ∞)) (n := n)).2 le_rfl, ?_⟩
      intro m
      refine le_iInf ?_
      intro hm
      refine WithTop.coe_le_coe.mpr <| Nat.succ_le_of_lt <| Nat.lt_of_not_ge ?_
      intro hmn
      apply hx
      rcases Nat.exists_eq_add_of_le hmn with ⟨k, rfl⟩
      rw [pow_add, mul_smul]
      calc
        p ^ m • p ^ k • x = p ^ k • (p ^ m • x) := by
          rw [smul_smul, smul_smul, Nat.mul_comm]
        _ = 0 := by simp [hm]
    exact not_lt_of_ge h hlt
end UlmsTheorem
