-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.normalizedOddGaussianRight_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:56:57.765052+00:00
-- url     : https://prove2.me/submissions/a4f15863-e21b-4491-a712-c76647bbf62a

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_gammaR_pos
import Theorems.Thm_SharpIntermediateSubgroupBounds_gammaR_le_one
import Theorems.Thm_SharpIntermediateSubgroupBounds_normalizedOddGaussianRight_eq
import Theorems.Thm_SharpIntermediateSubgroupBounds_eulerC_pos
import Theorems.Thm_SharpIntermediateSubgroupBounds_gammaR_inv_lt_eulerC


set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p a j : ℕ} (hp : 2 ≤ p) :
    normalizedOddGaussianRight p a j ≤
      eulerC (p : ℝ) ^ 2 * (p : ℝ)⁻¹ ^ (j * (j + 1)) := by
  by_cases hj : j ≤ a
  · rw [normalizedOddGaussianRight_eq hp hj]
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
    have hpow : 0 ≤ (p : ℝ)⁻¹ ^ (j * (j + 1)) :=
      pow_nonneg (inv_nonneg.mpr (by linarith)) _
    have hgam : 0 ≤ gammaR (p : ℝ) (2 * a + 1) := (gammaR_pos hp1 _).le
    have hplus : 0 ≤ (gammaR (p : ℝ) (a + 1 + j))⁻¹ :=
      (inv_pos.mpr (gammaR_pos hp1 _)).le
    have hminus : 0 ≤ (gammaR (p : ℝ) (a - j))⁻¹ :=
      (inv_pos.mpr (gammaR_pos hp1 _)).le
    calc
      (p : ℝ)⁻¹ ^ (j * (j + 1)) * gammaR (p : ℝ) (2 * a + 1) *
            (gammaR (p : ℝ) (a + 1 + j))⁻¹ *
              (gammaR (p : ℝ) (a - j))⁻¹ ≤
          (p : ℝ)⁻¹ ^ (j * (j + 1)) * 1 *
            (gammaR (p : ℝ) (a + 1 + j))⁻¹ *
              (gammaR (p : ℝ) (a - j))⁻¹ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (gammaR_le_one hp1 _) hpow) hplus) hminus
      _ ≤ (p : ℝ)⁻¹ ^ (j * (j + 1)) * 1 * eulerC (p : ℝ) *
            (gammaR (p : ℝ) (a - j))⁻¹ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (gammaR_inv_lt_eulerC hpR _).le
            (mul_nonneg hpow zero_le_one)) hminus
      _ ≤ (p : ℝ)⁻¹ ^ (j * (j + 1)) * 1 * eulerC (p : ℝ) *
            eulerC (p : ℝ) := by
        exact mul_le_mul_of_nonneg_left (gammaR_inv_lt_eulerC hpR _).le
          (mul_nonneg (mul_nonneg hpow zero_le_one) (eulerC_pos hpR).le)
      _ = eulerC (p : ℝ) ^ 2 * (p : ℝ)⁻¹ ^ (j * (j + 1)) := by ring
  · rw [normalizedOddGaussianRight, if_neg hj]
    exact mul_nonneg (sq_nonneg _) (pow_nonneg (inv_nonneg.mpr (by positivity)) _)
end SharpIntermediateSubgroupBounds
