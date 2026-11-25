-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.radJ_add_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:05:57.698539+00:00
-- url     : https://prove2.me/submissions/0110cfda-b948-45cb-827e-a3b98d5eaad2

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_radJ_eq

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
open MeasureTheory Set Real Filter Topology
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (k : ℕ) : radJ (k + 2) = ((k : ℝ) + 1) / 2 * radJ k := by
  rw [radJ_eq, radJ_eq]
  have h : (((k + 2 : ℕ) : ℝ) + 1) / 2 = ((k : ℝ) + 1) / 2 + 1 := by push_cast; ring
  rw [h, Real.Gamma_add_one (by positivity)]
  ring
end ReciprocityTheory.MultiplicativeHeights
