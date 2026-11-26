-- Prove2me | solution 1 for continuous_circleKernel_add_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:01:47.096909+00:00
-- url     : https://prove2.me/submissions/0e67b719-0d06-493b-95c8-4ccbea11bea5

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Definitions.Def_Operator_Crouzeix_CircleKernel
import Theorems.Thm_continuous_circleKernel

set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution (A : E →L[ℂ] E) {c : ℂ} {R : ℝ}
    (hρ : Metric.sphere c R ⊆ resolventSet ℂ A) (hR : 0 ≤ R) :
    Continuous (fun t : ℝ =>
      (-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t) +
        ContinuousLinearMap.adjoint ((-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t))) :=
  (continuous_circleKernel A hρ hR).add
    ((ContinuousLinearMap.adjoint : (E →L[ℂ] E) ≃ₗᵢ⋆[ℂ] (E →L[ℂ] E)).continuous.comp
      (continuous_circleKernel A hρ hR))
