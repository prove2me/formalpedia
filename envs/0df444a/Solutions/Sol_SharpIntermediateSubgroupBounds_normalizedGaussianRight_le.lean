-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.normalizedGaussianRight_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:56:42.6254+00:00
-- url     : https://prove2.me/submissions/4fe33d12-779d-4ebe-9e1d-447eabfe89a6

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_gammaR_pos
import Theorems.Thm_SharpIntermediateSubgroupBounds_gammaR_le_one
import Theorems.Thm_SharpIntermediateSubgroupBounds_normalizedGaussianRight_eq
import Theorems.Thm_SharpIntermediateSubgroupBounds_eulerC_pos
import Theorems.Thm_SharpIntermediateSubgroupBounds_gammaR_inv_lt_eulerC


set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p a j : ℕ} (hp : 2 ≤ p) :
    normalizedGaussianRight p a j ≤
      eulerC (p : ℝ) ^ 2 * (p : ℝ)⁻¹ ^ (j * j) := by
  by_cases hj : j ≤ a
  · rw [normalizedGaussianRight_eq hp hj]
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
    have hpow : 0 ≤ (p : ℝ)⁻¹ ^ (j * j) := pow_nonneg (inv_nonneg.mpr (by linarith)) _
    have hgam : 0 ≤ gammaR (p : ℝ) (2 * a) := (gammaR_pos hp1 _).le
    have hplus : 0 ≤ (gammaR (p : ℝ) (a + j))⁻¹ :=
      (inv_pos.mpr (gammaR_pos hp1 _)).le
    have hminus : 0 ≤ (gammaR (p : ℝ) (a - j))⁻¹ :=
      (inv_pos.mpr (gammaR_pos hp1 _)).le
    calc
      (p : ℝ)⁻¹ ^ (j * j) * gammaR (p : ℝ) (2 * a) *
            (gammaR (p : ℝ) (a + j))⁻¹ * (gammaR (p : ℝ) (a - j))⁻¹ ≤
          (p : ℝ)⁻¹ ^ (j * j) * 1 *
            (gammaR (p : ℝ) (a + j))⁻¹ *
              (gammaR (p : ℝ) (a - j))⁻¹ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (gammaR_le_one hp1 _) hpow) hplus)
          hminus
      _ ≤ (p : ℝ)⁻¹ ^ (j * j) * 1 * eulerC (p : ℝ) *
            (gammaR (p : ℝ) (a - j))⁻¹ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (gammaR_inv_lt_eulerC hpR _).le
            (mul_nonneg hpow zero_le_one)) hminus
      _ ≤ (p : ℝ)⁻¹ ^ (j * j) * 1 * eulerC (p : ℝ) *
            eulerC (p : ℝ) := by
        exact mul_le_mul_of_nonneg_left (gammaR_inv_lt_eulerC hpR _).le
          (mul_nonneg (mul_nonneg hpow zero_le_one) (eulerC_pos hpR).le)
      _ = eulerC (p : ℝ) ^ 2 * (p : ℝ)⁻¹ ^ (j * j) := by ring
  · rw [normalizedGaussianRight, if_neg hj]
    positivity
end SharpIntermediateSubgroupBounds
