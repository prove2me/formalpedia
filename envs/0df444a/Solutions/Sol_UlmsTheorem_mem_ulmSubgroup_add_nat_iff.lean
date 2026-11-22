-- Prove2me | solution 1 for UlmsTheorem.mem_ulmSubgroup_add_nat_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:54:48.289695+00:00
-- url     : https://prove2.me/submissions/f1d14fa5-6bd5-4792-8445-47dd361026b8

module
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.Algebra.Group.Subgroup.Map
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Subgroups
public import Mathlib.Algebra.Module.NatInt
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmSubgroups
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_zero
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_add_one_iff
public import Theorems.Thm_UlmsTheorem_mem_pImage
attribute [local simp] UlmsTheorem.mem_pImage


attribute [local simp] UlmsTheorem.ulmSubgroup_zero
attribute [local simp] UlmsTheorem.mem_ulmSubgroup_add_one_iff

set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal
variable (p : ℕ)
variable {G : Type*} [AddCommGroup G]
namespace UlmsTheorem
theorem _root_.solution (α : Ordinal) (n : ℕ) (x : G) :
    x ∈ ulmSubgroup p (α + n) (G := G) ↔
      ∃ y ∈ ulmSubgroup p α (G := G), p ^ n • y = x := by
  induction n generalizing x with
  | zero =>
      simp
  | succ n ih =>
      rw [show ((n + 1 : ℕ) : Ordinal) = (n : Ordinal) + 1 by simp,
        ← add_assoc, mem_ulmSubgroup_add_one_iff]
      constructor
      · rintro ⟨z, hz, rfl⟩
        rcases (ih z).1 hz with ⟨y, hy, rfl⟩
        refine ⟨y, hy, ?_⟩
        rw [pow_succ, mul_smul, smul_comm]
      · rintro ⟨y, hy, hxy⟩
        refine ⟨p ^ n • y, (ih _).2 ⟨y, hy, rfl⟩, ?_⟩
        rw [← hxy, pow_succ, mul_smul, smul_comm]
end UlmsTheorem
