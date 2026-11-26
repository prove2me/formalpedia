-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.tsum_oddGaussianLimitSummand_eq_oddGaussianConstant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:57:23.18412+00:00
-- url     : https://prove2.me/submissions/c73c54a8-d6bc-4993-abf2-b1a38731b2a5

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_shiftedTheta_half_eq_quarterShiftScale_mul_tsum

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) :
    ∑' j : ℕ, oddGaussianLimitSummand p j = oddGaussianConstant (p : ℝ) := by
  have htheta := shiftedTheta_half_eq_quarterShiftScale_mul_tsum hp
  unfold oddGaussianLimitSummand oddGaussianConstant
  calc
    (∑' j : ℕ, 2 * quarterShiftScale (p : ℝ) *
        (eulerC (p : ℝ) * (p : ℝ)⁻¹ ^ (j * (j + 1)))) =
        (2 * quarterShiftScale (p : ℝ) * eulerC (p : ℝ)) *
          ∑' j : ℕ, (p : ℝ)⁻¹ ^ (j * (j + 1)) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro j
      ring
    _ = eulerC (p : ℝ) *
        (quarterShiftScale (p : ℝ) *
          (2 * ∑' j : ℕ, (p : ℝ)⁻¹ ^ (j * (j + 1)))) := by ring
    _ = eulerC (p : ℝ) * shiftedTheta (p : ℝ) (1 / 2) := by rw [htheta]
end SharpIntermediateSubgroupBounds
