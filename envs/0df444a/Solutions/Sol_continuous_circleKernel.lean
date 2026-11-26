-- Prove2me | solution 1 for continuous_circleKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:00:44.621044+00:00
-- url     : https://prove2.me/submissions/3d867573-67df-4fd0-a8b8-e12eb225002e

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Definitions.Def_Operator_Crouzeix_CircleKernel
import Theorems.Thm_continuous_resolvent_circleMap
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution (A : E →L[ℂ] E) {c : ℂ} {R : ℝ}
    (hρ : Metric.sphere c R ⊆ resolventSet ℂ A) (hR : 0 ≤ R) :
    Continuous (fun t : ℝ => (-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t)) := by
  have hd : Continuous (fun t : ℝ => -I * deriv (circleMap c R) t) := by
    simp only [deriv_circleMap]
    fun_prop
  exact hd.smul (continuous_resolvent_circleMap A hρ hR)
