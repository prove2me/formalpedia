-- Prove2me | solution 1 for PsiMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:54:40.512805+00:00
-- url     : https://prove2.me/submissions/ab019eac-852c-40b2-811d-19e036893988

import Definitions.Def_Tablet_psi
import Definitions.Def_Tablet_CurveLenMeasurable
import Definitions.Def_Tablet_CurveScaledEvalMeasurable
import Definitions.Def_Tablet_PsiMeasurable
import Theorems.Thm_CurveLenMeasurable
import Theorems.Thm_CurveScaledEvalMeasurable


set_option autoImplicit false
open MeasureTheory
theorem _root_.solution {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (m : ℕ) (Q : Finset E) (ε C : ℝ) :
    Measurable (fun γ : Curve E => psi m Q ε C γ) := by
-- BODY
  have hlen : Measurable (fun γ : Curve E => γ.len) := CurveLenMeasurable
  have hinf : ∀ c : ℝ, Measurable
      (fun γ : Curve E => Metric.infDist (γ.toFun (c * γ.len)) (Q : Set E)) := by
    intro c
    exact (Metric.lipschitz_infDist_pt (Q : Set E)).continuous.measurable.comp
      (CurveScaledEvalMeasurable c)
  unfold psi
  refine Measurable.add (measurable_const.mul (Finset.measurable_sum _ (fun i _ => ?_))) ?_
  · refine Measurable.min (by fun_prop) ?_
    have h1 := hinf ((i : ℝ) / m)
    have h2 := hinf (((i : ℝ) - 1) / m)
    simp only [div_mul_eq_mul_div] at h1 h2
    exact measurable_const.add (measurable_const.mul (h1.add h2))
  · exact ((measurable_const.mul (hlen.pow_const 2)).div measurable_const)
