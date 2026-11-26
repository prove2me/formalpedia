-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.gaussian_odd_rank_rpow_asymptotic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:04:17.912901+00:00
-- url     : https://prove2.me/submissions/b92a08f1-ed0d-4060-bd06-58907fe27b3d

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_gaussian_odd_rank_asymptotic
import Theorems.Thm_SharpIntermediateSubgroupBounds_quarterShiftScale_mul_centered_power

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) :
    Tendsto (fun a : ℕ ↦
      Real.rpow (p : ℝ) (-(((2 * a + 1 : ℕ) : ℝ) ^ 2 / 4)) *
        (totalQBinom p (2 * a + 1) : ℝ)) atTop
      (nhds (oddGaussianConstant (p : ℝ))) := by
  apply (gaussian_odd_rank_asymptotic hp).congr'
  filter_upwards with a
  rw [quarterShiftScale_mul_centered_power hp]
end SharpIntermediateSubgroupBounds
