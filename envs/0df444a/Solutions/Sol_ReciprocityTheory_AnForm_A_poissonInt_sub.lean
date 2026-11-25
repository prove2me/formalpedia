-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.poissonInt_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:06:57.34401+00:00
-- url     : https://prove2.me/submissions/88f29c35-ce3f-4bc4-b5e2-8a74e6954cad

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshPoisson
import Theorems.Thm_ReciprocityTheory_AnForm_A_poissonKernel_zero_continuousOn
import Theorems.Thm_ReciprocityTheory_AnForm_A_circleAverage_poissonKernel_zero

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
theorem _root_.solution {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r) (hg : ContinuousOn g (sphere 0 r))
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) r) (c : ℝ) :
    poissonInt g r w - c =
      Real.circleAverage (fun z ↦ poissonKernel 0 w z * (g z - c)) 0 r := by
  have hP : CircleIntegrable (poissonKernel 0 w) 0 r :=
    (poissonKernel_zero_continuousOn hr hw).circleIntegrable hr.le
  have hPg : IntervalIntegrable
      (fun θ : ℝ ↦ poissonKernel 0 w (circleMap 0 r θ) * g (circleMap 0 r θ))
      MeasureTheory.volume 0 (2 * π) :=
    ((poissonKernel_zero_continuousOn hr hw).mul hg).circleIntegrable hr.le
  have hPc : IntervalIntegrable (fun θ : ℝ ↦ c * poissonKernel 0 w (circleMap 0 r θ))
      MeasureTheory.volume 0 (2 * π) := IntervalIntegrable.const_mul hP c
  have h1 := circleAverage_poissonKernel_zero (r := r) hw
  unfold Real.circleAverage at h1
  unfold poissonInt Real.circleAverage
  have hI : (∫ θ in (0 : ℝ)..2 * π, poissonKernel 0 w (circleMap 0 r θ) * (g (circleMap 0 r θ) - c)) =
      (∫ θ in (0 : ℝ)..2 * π, poissonKernel 0 w (circleMap 0 r θ) * g (circleMap 0 r θ)) -
        c * ∫ θ in (0 : ℝ)..2 * π, poissonKernel 0 w (circleMap 0 r θ) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hPg hPc]
    congr 1
    funext θ
    ring
  simp only [Pi.smul_apply, smul_eq_mul] at h1 ⊢
  rw [hI]
  linear_combination c * h1
end ReciprocityTheory.AnForm.A
