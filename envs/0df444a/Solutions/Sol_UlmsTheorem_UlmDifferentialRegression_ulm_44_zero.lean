-- Prove2me | solution 1 for UlmsTheorem.UlmDifferentialRegression.ulm_44_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:58:58.726444+00:00
-- url     : https://prove2.me/submissions/09cbe0d7-775c-44e7-a31d-9a20588cca70

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
theorem _root_.solution : ulmInvariant 2 (0 : Ordinal) (G := ZMod 4 × ZMod 4) = 0 := by
  have hsub : pSocleAt 2 (0 : Ordinal) (G := ZMod 4 × ZMod 4)
      ≤ pSocleAt 2 (Order.succ (0 : Ordinal)) (G := ZMod 4 × ZMod 4) := by
    intro x hx
    rw [mem_pSocleAt] at hx ⊢
    refine ⟨hx.1, ?_⟩
    have h1 : Order.succ (0 : Ordinal) = ((1 : ℕ) : Ordinal) := by simp
    rw [h1, ulmSubgroup_nat]
    obtain ⟨hp, -⟩ := hx
    simp only [pPow, AddSubgroup.mem_mk, Set.mem_ofPred_eq, AddSubsemigroup.mem_mk,
      AddSubmonoid.mem_mk]
    revert hp
    revert x
    decide
  have htop : ulmDenSubmodule 2 (0 : Ordinal) (G := ZMod 4 × ZMod 4) = ⊤ := by
    ext y
    simp only [Submodule.mem_top, iff_true]
    exact hsub y.2
  have hss : Subsingleton (ulmQuotient 2 (0 : Ordinal) (G := ZMod 4 × ZMod 4)) := by
    rw [ulmQuotient, htop]
    infer_instance
  rw [ulmInvariant]
  exact rank_zero_iff.mpr hss
end UlmsTheorem.UlmDifferentialRegression
