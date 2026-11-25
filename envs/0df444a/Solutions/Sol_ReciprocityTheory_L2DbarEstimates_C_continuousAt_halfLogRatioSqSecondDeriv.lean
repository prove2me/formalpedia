-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.continuousAt_halfLogRatioSqSecondDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:02:29.60228+00:00
-- url     : https://prove2.me/submissions/6247adeb-8136-486a-9ec8-8b464ce77125

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_hasDerivAt_cutL

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
theorem _root_.solution {ε s : ℝ} (h : 0 < s + ε) : ContinuousAt (halfLogRatioSqSecondDeriv ε) s := by
  show ContinuousAt (fun s => (1 - cutL ε s) / (s + ε) ^ 2) s
  exact (continuousAt_const.sub (hasDerivAt_cutL h).continuousAt).div (by fun_prop)
    (pow_ne_zero 2 h.ne')
end ReciprocityTheory.L2DbarEstimates.C
