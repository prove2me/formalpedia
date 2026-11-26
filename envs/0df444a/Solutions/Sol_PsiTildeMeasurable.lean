-- Prove2me | solution 1 for PsiTildeMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:56:06.511995+00:00
-- url     : https://prove2.me/submissions/b1d7e9ef-eed1-4ee4-b187-2ed38cf74df6

import Definitions.Def_Tablet_psiTilde
import Definitions.Def_Tablet_CurveLenMeasurable
import Definitions.Def_Tablet_CurveScaledEvalMeasurable
import Definitions.Def_Tablet_PsiTildeMeasurable
import Theorems.Thm_CurveLenMeasurable
import Theorems.Thm_CurveScaledEvalMeasurable


set_option autoImplicit false
open MeasureTheory
theorem _root_.solution {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (m : ℕ) (Q : Finset E) (ε C : ℝ) :
    Measurable (fun γ : Curve E => psiTilde m Q ε C γ) := by
-- BODY
  have hlen : Measurable (fun γ : Curve E => γ.len) := CurveLenMeasurable
  have hinf : ∀ c : ℝ, Measurable
      (fun γ : Curve E => Metric.infDist (γ.toFun (c * γ.len)) (Q : Set E)) := by
    intro c
    exact (Metric.lipschitz_infDist_pt (Q : Set E)).continuous.measurable.comp
      (CurveScaledEvalMeasurable c)
  unfold psiTilde
  refine Measurable.add ((measurable_const.mul (hlen.pow_const 2)).div measurable_const) ?_
  refine Measurable.mul (by fun_prop) (Finset.measurable_sum _ (fun i _ => ?_))
  refine Measurable.min measurable_const ?_
  have h1 := hinf ((i : ℝ) / m)
  simp only [div_mul_eq_mul_div] at h1
  exact measurable_const.add (measurable_const.mul h1)
