-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.norm_circPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:31:52.287442+00:00
-- url     : https://prove2.me/submissions/1cb23fd3-cb21-46b6-92e8-04e2fba7273e

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_circPt_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Polynomial Real
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (t : ℝ) : ‖circPt t‖ = 1 := by
  rw [circPt_eq, norm_circleMap_zero]; simp
end ReciprocityTheory.MultiplicativeHeights
