-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.bI_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:01:10.835131+00:00
-- url     : https://prove2.me/submissions/9b6a2f89-172f-4001-8d5f-61fc069afcb6

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_LogDetSt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Matrix MeasureTheory
open scoped ComplexOrder
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (j : ℕ) : ((j : ℝ) + 1) * betaNatInt 0 j = 1 := by
  unfold betaNatInt
  simp only [pow_zero, one_mul]
  have h := intervalIntegral.integral_comp_sub_left (f := fun x : ℝ => x ^ j) (a := 0) (b := 1) 1
  simp only [sub_zero, sub_self] at h
  rw [h, integral_pow]
  have hj : (j : ℝ) + 1 ≠ 0 := by positivity
  simp
  field_simp
end ReciprocityTheory.GeometryOfNumbersTheory
