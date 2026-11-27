-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.integral_bernstein
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:29:17.64787+00:00
-- url     : https://prove2.me/submissions/31587882-119f-46ec-aef4-3df6754f22f6

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_LogDetSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_bI_closed

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
theorem _root_.solution (D i : ℕ) (hi : i ≤ D) :
    ∫ t in (0 : ℝ)..1, (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) = 1 / (D + 1 : ℝ) := by
  have h := bI_closed i (D - i)
  have e : i + (D - i) = D := by omega
  rw [e] at h
  have hcast : ((i:ℝ) + ((D - i : ℕ) : ℝ) + 1) = (D:ℝ) + 1 := by
    rw [Nat.cast_sub hi]; ring
  rw [hcast] at h
  unfold betaNatInt at h
  have hD : (D:ℝ) + 1 ≠ 0 := by positivity
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul, eq_div_iff hD]
  linear_combination h
end ReciprocityTheory.GeometryOfNumbersTheory
