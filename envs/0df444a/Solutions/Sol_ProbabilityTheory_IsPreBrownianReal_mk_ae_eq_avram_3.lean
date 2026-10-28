-- Prove2me | solution 3 for ProbabilityTheory.IsPreBrownianReal.mk_ae_eq_avram
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:30:52.025833+00:00
-- url     : https://prove2.me/submissions/ee04642d-da4d-49a0-981d-c7ac15e4c827

import Definitions.Def_KLSModular_BrownianMotion_Gaussian_BrownianMotion

open ProbabilityTheory MeasureTheory NNReal
open scoped NNReal
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : ℝ≥0 → Ω → ℝ) (h : IsPreBrownianReal X P) (t : ℝ≥0) :
    h.mk X t =ᵐ[P] X t :=
  h.exists_continuous_modification.choose_spec.2.1 t
