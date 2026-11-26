-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.evenUSummand_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:58:27.096319+00:00
-- url     : https://prove2.me/submissions/053877e4-3e0f-457d-9b70-74b655e9f05e

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_eulerC_pos
import Theorems.Thm_SharpIntermediateSubgroupBounds_gammaR_inv_lt_eulerC


set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p a j : ℕ} (hp : 2 ≤ p) :
    evenUSummand p a j ≤
      2 * eulerC (p : ℝ) * (p : ℝ)⁻¹ ^ (j * j) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  unfold evenUSummand
  by_cases hj0 : j = 0
  · subst j
    simp only [if_pos, Nat.zero_mul, pow_zero, mul_one]
    linarith [gammaR_inv_lt_eulerC hpR a, eulerC_pos hpR]
  · rw [if_neg hj0]
    by_cases hja : j ≤ a
    · rw [if_pos hja]
      have hpow : 0 ≤ (p : ℝ)⁻¹ ^ (j * j) := by positivity
      have hsum : (gammaR (p : ℝ) (a + j))⁻¹ +
          (gammaR (p : ℝ) (a - j))⁻¹ ≤ 2 * eulerC (p : ℝ) := by
        linarith [gammaR_inv_lt_eulerC hpR (a + j),
          gammaR_inv_lt_eulerC hpR (a - j)]
      nlinarith
    · rw [if_neg hja]
      exact mul_nonneg (mul_nonneg (by norm_num) (eulerC_pos hpR).le) (by positivity)
end SharpIntermediateSubgroupBounds
