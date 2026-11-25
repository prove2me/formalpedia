-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.continuousAt_halfLogRatioSqDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:02:24.38493+00:00
-- url     : https://prove2.me/submissions/4d72e078-81c2-4c38-a44b-fecb7c9fe4bb

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_hasDerivAt_halfLogRatioSqDeriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {ε s : ℝ} (h : 0 < s + ε) : ContinuousAt (halfLogRatioSqDeriv ε) s :=
  (hasDerivAt_halfLogRatioSqDeriv h).continuousAt
end ReciprocityTheory.L2DbarEstimates.C
