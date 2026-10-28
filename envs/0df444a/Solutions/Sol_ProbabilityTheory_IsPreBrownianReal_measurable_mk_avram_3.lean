-- Prove2me | solution 3 for ProbabilityTheory.IsPreBrownianReal.measurable_mk_avram
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:30:47.263688+00:00
-- url     : https://prove2.me/submissions/4356248b-8c4c-4a85-9fb8-5d95d2e9ee64

import Definitions.Def_KLSModular_BrownianMotion_Gaussian_BrownianMotion

open ProbabilityTheory MeasureTheory NNReal
open scoped NNReal
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : ℝ≥0 → Ω → ℝ) (h : IsPreBrownianReal X P) (t : ℝ≥0) :
    Measurable (h.mk X t) :=
  h.exists_continuous_modification.choose_spec.1 t
