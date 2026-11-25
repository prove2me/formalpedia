-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.circPt_injOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:01:24.989801+00:00
-- url     : https://prove2.me/submissions/4c9060cb-9863-4c02-85c9-7b42752ca9b7

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
theorem _root_.solution : Set.InjOn circPt (Set.Ioc (0 : ℝ) 1) := by
  intro a ha b hb h
  simp only [circPt_eq] at h
  have hinj := injOn_circleMap_of_abs_sub_le (c := (0 : ℂ)) (R := 1) one_ne_zero
    (a := 0) (b := 2 * π) (by rw [zero_sub, abs_neg, abs_of_pos (by positivity)])
  rw [Set.uIoc_of_le (by positivity)] at hinj
  have : 2 * π * a = 2 * π * b := by
    apply hinj
    · constructor <;> nlinarith [ha.1, ha.2, pi_pos]
    · constructor <;> nlinarith [hb.1, hb.2, pi_pos]
    · exact h
  have hpi : (2 * π) ≠ 0 := by positivity
  exact mul_left_cancel₀ hpi this
end ReciprocityTheory.MultiplicativeHeights
