-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.discI_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:29:52.913435+00:00
-- url     : https://prove2.me/submissions/fb6fbed9-98c7-4a11-89b4-2e854648c0f4

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
theorem _root_.solution {a R t : ℝ} (ha : 0 ≤ a) (hR : 0 ≤ R) (ht : 0 < t) :
    discI (t * a) (R / Real.sqrt t) = discI a R / t := by
  have hs : (R / Real.sqrt t) ^ 2 = R ^ 2 / t := by
    rw [div_pow, Real.sq_sqrt ht.le]
  have hR' : 0 ≤ R / Real.sqrt t := div_nonneg hR (Real.sqrt_nonneg t)
  rcases ha.lt_or_eq with ha | ha
  · rw [discI_of_pos (mul_pos ht ha) hR', discI_of_pos ha hR, hs]
    have : t * a * (R ^ 2 / t) = a * R ^ 2 := by field_simp
    rw [this]
    field_simp
  · subst ha; rw [mul_zero, discI_zero hR', discI_zero hR, hs]; ring
end ReciprocityTheory.GeometryOfNumbersTheory
