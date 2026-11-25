-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.discI_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:29:50.570824+00:00
-- url     : https://prove2.me/submissions/bb97aa60-38ab-421b-9cc5-625f472a0487

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_DiscSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_discI_of_pos
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_discI_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Filter Topology
open Set
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {a R : ℝ} (ha : 0 ≤ a) (hR : 0 < R) : 0 < discI a R := by
  rcases ha.lt_or_eq with ha | ha
  · rw [discI_of_pos ha hR.le]
    have : Real.exp (-(a * R ^ 2)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [sq_pos_of_pos hR])
    have := Real.pi_pos
    apply div_pos _ ha
    nlinarith
  · subst ha; rw [discI_zero hR.le]; have := Real.pi_pos; positivity
end ReciprocityTheory.GeometryOfNumbersTheory
