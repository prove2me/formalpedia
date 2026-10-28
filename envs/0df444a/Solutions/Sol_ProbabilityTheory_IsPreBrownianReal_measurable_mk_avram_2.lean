-- Prove2me | solution 2 for ProbabilityTheory.IsPreBrownianReal.measurable_mk_avram
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:30:41.407935+00:00
-- url     : https://prove2.me/submissions/e07da2dc-15e9-407a-8fb6-599857c525e3

import Definitions.Def_KLSModular_BrownianMotion_Gaussian_BrownianMotion

open ProbabilityTheory MeasureTheory NNReal
open scoped NNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : ℝ≥0 → Ω → ℝ) (h : IsPreBrownianReal X P) (t : ℝ≥0) :
    Measurable (h.mk X t) := by
  exact h.exists_continuous_modification.choose_spec.1 t
