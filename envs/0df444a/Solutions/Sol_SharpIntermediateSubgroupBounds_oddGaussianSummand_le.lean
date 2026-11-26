-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.oddGaussianSummand_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:58:00.194596+00:00
-- url     : https://prove2.me/submissions/46b60d71-4300-4ea0-b27d-ceb470f5bbd3

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_normalizedOddGaussianRight_le

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p a j : ℕ} (hp : 2 ≤ p) :
    oddGaussianSummand p a j ≤
      2 * quarterShiftScale (p : ℝ) * eulerC (p : ℝ) ^ 2 *
        (p : ℝ)⁻¹ ^ (j * (j + 1)) := by
  unfold oddGaussianSummand
  have hs : 0 ≤ 2 * quarterShiftScale (p : ℝ) :=
    mul_nonneg (by norm_num) (Real.exp_pos _).le
  calc
    2 * quarterShiftScale (p : ℝ) * normalizedOddGaussianRight p a j ≤
        2 * quarterShiftScale (p : ℝ) *
          (eulerC (p : ℝ) ^ 2 * (p : ℝ)⁻¹ ^ (j * (j + 1))) :=
      mul_le_mul_of_nonneg_left (normalizedOddGaussianRight_le hp) hs
    _ = 2 * quarterShiftScale (p : ℝ) * eulerC (p : ℝ) ^ 2 *
          (p : ℝ)⁻¹ ^ (j * (j + 1)) := by ring
end SharpIntermediateSubgroupBounds
