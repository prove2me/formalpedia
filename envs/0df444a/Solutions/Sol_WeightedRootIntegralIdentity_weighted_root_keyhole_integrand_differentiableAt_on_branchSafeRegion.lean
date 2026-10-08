-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weighted_root_keyhole_integrand_differentiableAt_on_branchSafeRegion
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-18T22:27:55.602098+00:00
-- url     : https://prove2.me/submissions/ae69d89d-239b-42fc-bff8-7f5d1137ad06

import Mathlib
import Definitions.Def_weightedRootBranchSafeRegion
import Definitions.Def_weightedRootKeyholeIntegrand
import Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_differentiableAt_of_shift_mem_slitPlane
open scoped BigOperators

theorem solution
    (n : ℕ) (a w : ℕ → ℝ) (r R : ℝ) (z : ℂ)
    (hr : 0 < r) (hz : z ∈ weightedRootBranchSafeRegion n a r R) :
    DifferentiableAt ℂ (weightedRootKeyholeIntegrand n a w) z := by
  have hF : DifferentiableAt ℂ
      (fun z : ℂ => ∏ i ∈ Finset.range n,
        (z - (a i : ℂ)) ^ (w i : ℂ)) z := by
    apply WeightedRootIntegralIdentity.weighted_root_differentiableAt_of_shift_mem_slitPlane
    intro i hi
    exact hz.2.2 i hi
  have hz0 : z ≠ 0 := by
    intro hzero
    have hnz : ‖z‖ = 0 := by simp [hzero]
    linarith [hz.1]
  change DifferentiableAt ℂ
    (fun z : ℂ =>
      (∏ i ∈ Finset.range n, (z - (a i : ℂ)) ^ (w i : ℂ)) / z) z
  exact hF.div differentiableAt_id hz0
