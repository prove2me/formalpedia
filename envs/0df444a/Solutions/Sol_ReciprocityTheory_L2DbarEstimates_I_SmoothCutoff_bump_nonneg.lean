-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.SmoothCutoff.bump_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:34:19.523811+00:00
-- url     : https://prove2.me/submissions/03d399b4-da36-476a-a653-edc5a1b2d084

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_Cutoff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
open ReciprocityTheory.L2DbarEstimates.I.SmoothCutoff
namespace ReciprocityTheory.L2DbarEstimates.I.SmoothCutoff
theorem _root_.solution (s : ℝ) : 0 ≤ bump s :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
end ReciprocityTheory.L2DbarEstimates.I.SmoothCutoff
