-- Prove2me | solution 1 for OpenQuantumProblem35.uniformCoeff_mul_star
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:07:58.580009+00:00
-- url     : https://prove2.me/submissions/374d69a7-17bb-44a1-a317-c4ca49a1e373

module
public import Mathlib
public import Definitions.Def_AME125_Defs
public import Theorems.Thm_OpenQuantumProblem35_mkStateVector_apply
public import Theorems.Thm_OpenQuantumProblem35_permuteState_apply
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_leftIndex
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_rightIndex
public import Theorems.Thm_OpenQuantumProblem35_card_config
public import Theorems.Thm_OpenQuantumProblem35_diagonalState_apply
public import Theorems.Thm_OpenQuantumProblem35_uniformCoeff_norm_sq
attribute [local simp] OpenQuantumProblem35.mkStateVector_apply
attribute [local simp] OpenQuantumProblem35.permuteState_apply
attribute [local simp] OpenQuantumProblem35.combineFirst_leftIndex
attribute [local simp] OpenQuantumProblem35.combineFirst_rightIndex
attribute [local simp] OpenQuantumProblem35.card_config
attribute [local simp] OpenQuantumProblem35.diagonalState_apply

set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35
namespace OpenQuantumProblem35
theorem _root_.solution (d : ℕ) :
    uniformCoeff d * star (uniformCoeff d) = ((d : ℂ)⁻¹) := by
  calc
    uniformCoeff d * star (uniformCoeff d) = ((‖uniformCoeff d‖ ^ 2 : ℝ) : ℂ) := by
      simpa [RCLike.star_def] using (RCLike.mul_conj (uniformCoeff d))
    _ = (((d : ℝ)⁻¹ : ℝ) : ℂ) := by
      rw [uniformCoeff_norm_sq]
    _ = ((d : ℂ)⁻¹) := by
      simp [Complex.ofReal_inv]
end OpenQuantumProblem35
