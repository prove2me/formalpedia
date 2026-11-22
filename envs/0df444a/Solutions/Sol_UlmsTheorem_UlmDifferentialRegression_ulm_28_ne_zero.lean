-- Prove2me | solution 1 for UlmsTheorem.UlmDifferentialRegression.ulm_28_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:58:59.149764+00:00
-- url     : https://prove2.me/submissions/962565b8-84a9-4060-9b95-e8841829c035

module
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmInvariants
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Theorem
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_UlmsTheorem_Regression
public import Theorems.Thm_UlmsTheorem_mem_pImage
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_add_one_iff
public import Theorems.Thm_UlmsTheorem_pHeight_zero
public import Theorems.Thm_UlmsTheorem_pOrder_zero
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_nat
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_zero
attribute [local simp] UlmsTheorem.mem_pImage
attribute [local simp] UlmsTheorem.mem_ulmSubgroup_add_one_iff
attribute [local simp] UlmsTheorem.pHeight_zero
attribute [local simp] UlmsTheorem.pOrder_zero
attribute [local simp] UlmsTheorem.ulmSubgroup_zero



set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open UlmsTheorem.UlmDifferentialRegression
attribute [local instance] UlmsTheorem.UlmDifferentialRegression._p2m_local_instance_ed668a12d5_64
namespace UlmsTheorem.UlmDifferentialRegression
theorem _root_.solution : ulmInvariant 2 (0 : Ordinal) (G := ZMod 2 × ZMod 8) ≠ 0 := by
  have hmem : ((1 : ZMod 2), (0 : ZMod 8)) ∈ pSocleAt 2 (0 : Ordinal) (G := ZMod 2 × ZMod 8) := by
    rw [mem_pSocleAt]
    refine ⟨by decide, ?_⟩
    simp [ulmSubgroup_zero]
  set x : pSocleAt 2 (0 : Ordinal) (G := ZMod 2 × ZMod 8) := ⟨_, hmem⟩ with hx
  have hnot : x ∉ ulmDenSubmodule 2 (0 : Ordinal) (G := ZMod 2 × ZMod 8) := by
    intro hcon
    have : ((1 : ZMod 2), (0 : ZMod 8))
        ∈ pSocleAt 2 (Order.succ (0 : Ordinal)) (G := ZMod 2 × ZMod 8) := hcon
    rw [mem_pSocleAt] at this
    obtain ⟨-, hin⟩ := this
    have h1 : Order.succ (0 : Ordinal) = ((1 : ℕ) : Ordinal) := by simp
    rw [h1, ulmSubgroup_nat] at hin
    simp only [pPow, AddSubgroup.mem_mk, Set.mem_ofPred_eq, AddSubsemigroup.mem_mk,
      AddSubmonoid.mem_mk] at hin
    revert hin
    decide
  let _ : Nontrivial (ulmQuotient 2 (0 : Ordinal) (G := ZMod 2 × ZMod 8)) := by
    refine ⟨Submodule.Quotient.mk x, 0, ?_⟩
    simpa [Submodule.Quotient.mk_eq_zero] using hnot
  rw [ulmInvariant]
  exact ne_of_gt rank_pos
end UlmsTheorem.UlmDifferentialRegression
