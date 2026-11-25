-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.continuousOn_cutComp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:02:33.88074+00:00
-- url     : https://prove2.me/submissions/1a9c03d8-7902-4c89-9570-329fcccc197d

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutB

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
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {T : Set (V n)} {F : V n → ℂ} (hFc : ContinuousOn F T) {g : ℝ → ℝ}
    (hg : ∀ s, 0 ≤ s → ContinuousAt g s) : ContinuousOn (fun z => g (‖F z‖ ^ 2)) T := by
  intro z hz
  have h1 : ContinuousWithinAt (fun z => ‖F z‖ ^ 2) T z := ((hFc z hz).norm).pow 2
  exact (hg _ (by positivity)).comp_continuousWithinAt h1
end ReciprocityTheory.L2DbarEstimates.C
