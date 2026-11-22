-- Prove2me | solution 1 for UlmsTheorem.UlmDifferentialRegression.no_iso_44_28
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:07:05.887188+00:00
-- url     : https://prove2.me/submissions/6abf67e7-71a1-499a-8f6c-de1960573e35

module
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmInvariants
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Theorem
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_UlmsTheorem_Regression
public import Theorems.Thm_UlmsTheorem_UlmDifferentialRegression_ulm_44_zero
public import Theorems.Thm_UlmsTheorem_UlmDifferentialRegression_ulm_28_ne_zero
public import Theorems.Thm_UlmsTheorem_mem_pImage
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_add_one_iff
public import Theorems.Thm_UlmsTheorem_pHeight_zero
public import Theorems.Thm_UlmsTheorem_pOrder_zero
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_nat
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_zero
public import Theorems.Thm_UlmsTheorem_ulm_theorem
attribute [local simp] UlmsTheorem.mem_pImage
attribute [local simp] UlmsTheorem.mem_ulmSubgroup_add_one_iff
attribute [local simp] UlmsTheorem.pHeight_zero
attribute [local simp] UlmsTheorem.pOrder_zero
attribute [local simp] UlmsTheorem.ulmSubgroup_zero


section
@[expose] public section
namespace UlmsTheorem
namespace UlmDifferentialRegression
section Witnesses
private lemma reduced_44 : IsReducedPGroup 2 (ZMod 4 × ZMod 4) where
  primary := fun x ↦ ⟨2, by revert x; decide⟩
  reduced := by
    refine ⟨((2 : ℕ) : Ordinal), ?_⟩
    rw [ulmSubgroup_nat]
    ext x
    simp only [pPow, AddSubgroup.mem_mk, Set.mem_ofPred_eq, AddSubgroup.mem_bot,
      AddSubsemigroup.mem_mk, AddSubmonoid.mem_mk]
    constructor
    · rintro ⟨y, rfl⟩; revert y; decide
    · rintro rfl; exact ⟨0, by decide⟩
private lemma reduced_28 : IsReducedPGroup 2 (ZMod 2 × ZMod 8) where
  primary := fun x ↦ ⟨3, by revert x; decide⟩
  reduced := by
    refine ⟨((3 : ℕ) : Ordinal), ?_⟩
    rw [ulmSubgroup_nat]
    ext x
    simp only [pPow, AddSubgroup.mem_mk, Set.mem_ofPred_eq, AddSubgroup.mem_bot,
      AddSubsemigroup.mem_mk, AddSubmonoid.mem_mk]
    constructor
    · rintro ⟨y, rfl⟩; revert y; decide
    · rintro rfl; exact ⟨0, by decide⟩
end Witnesses
end UlmDifferentialRegression
end UlmsTheorem
end
end

set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open UlmsTheorem.UlmDifferentialRegression
attribute [local instance] UlmsTheorem.UlmDifferentialRegression._p2m_local_instance_ed668a12d5_64
namespace UlmsTheorem.UlmDifferentialRegression
theorem _root_.solution : ¬ Nonempty ((ZMod 4 × ZMod 4) ≃+ (ZMod 2 × ZMod 8)) := by
  intro hiso
  have hall := (ulm_theorem 2 reduced_44 reduced_28).1 hiso
  have h0 := hall 0
  rw [ulm_44_zero] at h0
  exact ulm_28_ne_zero h0.symm
end UlmsTheorem.UlmDifferentialRegression
