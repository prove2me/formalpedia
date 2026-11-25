-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.cutP_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:18:21.554827+00:00
-- url     : https://prove2.me/submissions/e76cb062-a82e-47ef-b211-0b629de9b49a

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_cutL_nonneg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_cutL_mono

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
theorem _root_.solution {ε s t : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) (hst : s ≤ t) : cutP ε s ≤ cutP ε t := by
  unfold cutP
  nlinarith [cutL_nonneg hε hs, cutL_mono hε hs hst]
end ReciprocityTheory.L2DbarEstimates.C
