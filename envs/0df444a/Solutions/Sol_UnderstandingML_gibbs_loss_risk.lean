-- Prove2me | solution 1 for UnderstandingML.gibbs_loss_risk
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T11:49:54.599969+00:00
-- url     : https://prove2.me/submissions/a70ef8c4-e909-4607-8731-60b8643bc21b

import Mathlib
import Definitions.Def_UnderstandingML_PACBayes

set_option autoImplicit false

open MeasureTheory

open MeasureTheory UnderstandingML in
theorem solution {Z Hyp : Type*} [MeasurableSpace Z] [MeasurableSpace Hyp]
    (loss : Hyp → Z → ℝ) (hmeas : Measurable (Function.uncurry loss))
    (hloss : ∀ h z, loss h z ∈ Set.Icc (0 : ℝ) 1) (D : Measure Z) [IsProbabilityMeasure D]
    (Q : Measure Hyp) [IsProbabilityMeasure Q] :
    ∫ z, gibbsLoss loss Q z ∂D = gibbsRisk loss D Q := by
  unfold gibbsLoss gibbsRisk risk
  have hm : Measurable (Function.uncurry fun (z : Z) (h : Hyp) => loss h z) :=
    hmeas.comp measurable_swap
  have hint : Integrable (Function.uncurry fun (z : Z) (h : Hyp) => loss h z) (D.prod Q) := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    obtain ⟨h0, h1⟩ := hloss p.2 p.1
    rw [Real.norm_eq_abs]
    show |loss p.2 p.1| ≤ 1
    rw [abs_of_nonneg h0]
    exact h1
  exact integral_integral_swap hint
