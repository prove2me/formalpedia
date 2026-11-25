-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.ap_pt_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:14:33.675938+00:00
-- url     : https://prove2.me/submissions/4146a398-18fb-4b32-bd25-40db99e55d38

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution (u E η X : ℝ) (hη : 0 < η) :
    (Real.sqrt 0 + u * Real.sqrt ((X + 1) ^ 2 / ((X + 1) ^ 2 + η))) ^ 2 * (E / η) =
      u ^ 2 * (E / η) - u ^ 2 * (E / ((X + 1) ^ 2 + η)) := by
  have hD : 0 < (X + 1) ^ 2 + η := by positivity
  rw [Real.sqrt_zero, zero_add, mul_pow, Real.sq_sqrt (by positivity)]
  field_simp
  ring
end ReciprocityTheory.L2DbarEstimates.I
