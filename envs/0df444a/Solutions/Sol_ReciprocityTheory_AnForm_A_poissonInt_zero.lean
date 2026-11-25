-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.poissonInt_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:05:43.475263+00:00
-- url     : https://prove2.me/submissions/4ad10d31-bc57-4e8f-acd3-a86f18e5aa05

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshPoisson

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Metric Real Filter Topology InnerProductSpace
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r) :
    poissonInt g r 0 = Real.circleAverage g 0 r := by
  unfold poissonInt
  apply Real.circleAverage_congr_sphere
  intro z hz
  rw [mem_sphere_zero_iff_norm, abs_of_pos hr] at hz
  have hz0 : ‖z‖ ≠ 0 := by rw [hz]; exact hr.ne'
  simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, poissonKernel_def, sub_zero, norm_zero]
  rw [div_mul_eq_mul_div, div_eq_iff (pow_ne_zero 2 hz0)]
  ring
end ReciprocityTheory.AnForm.A
