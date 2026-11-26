-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.normalizedGaussianRight_le_eulerC
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:56:50.794795+00:00
-- url     : https://prove2.me/submissions/cf189c28-5c7f-40e2-8149-c34a69e88872

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_gammaR_pos
import Theorems.Thm_SharpIntermediateSubgroupBounds_gammaR_antitone
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
      eulerC (p : ℝ) * (p : ℝ)⁻¹ ^ (j * j) := by
  by_cases hj : j ≤ a
  · rw [normalizedGaussianRight_eq hp hj]
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
    have hpow : 0 ≤ (p : ℝ)⁻¹ ^ (j * j) := by positivity
    have hpluspos : 0 < gammaR (p : ℝ) (a + j) := gammaR_pos hp1 _
    have hratio_nonneg : 0 ≤ gammaR (p : ℝ) (2 * a) *
        (gammaR (p : ℝ) (a + j))⁻¹ :=
      mul_nonneg (gammaR_pos hp1 _).le (inv_pos.mpr hpluspos).le
    have hratio : gammaR (p : ℝ) (2 * a) *
        (gammaR (p : ℝ) (a + j))⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv]
      exact (div_le_one hpluspos).2 (gammaR_antitone hp1 (by omega))
    have hminus : 0 ≤ (gammaR (p : ℝ) (a - j))⁻¹ :=
      (inv_pos.mpr (gammaR_pos hp1 _)).le
    calc
      (p : ℝ)⁻¹ ^ (j * j) * gammaR (p : ℝ) (2 * a) *
          (gammaR (p : ℝ) (a + j))⁻¹ *
            (gammaR (p : ℝ) (a - j))⁻¹ =
        (p : ℝ)⁻¹ ^ (j * j) *
          (gammaR (p : ℝ) (2 * a) *
            (gammaR (p : ℝ) (a + j))⁻¹) *
              (gammaR (p : ℝ) (a - j))⁻¹ := by ring
      _ ≤ (p : ℝ)⁻¹ ^ (j * j) * 1 *
            (gammaR (p : ℝ) (a - j))⁻¹ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hratio hpow) hminus
      _ ≤ (p : ℝ)⁻¹ ^ (j * j) * 1 * eulerC (p : ℝ) := by
        exact mul_le_mul_of_nonneg_left (gammaR_inv_lt_eulerC hpR _).le
          (mul_nonneg hpow zero_le_one)
      _ = eulerC (p : ℝ) * (p : ℝ)⁻¹ ^ (j * j) := by ring
  · rw [normalizedGaussianRight, if_neg hj]
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    exact mul_nonneg (eulerC_pos hpR).le (by positivity)
end SharpIntermediateSubgroupBounds
