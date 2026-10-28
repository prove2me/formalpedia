-- Prove2me | solution 1 for ProbabilityTheory.IsPreBrownianReal.measurable_mk_avram
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:30:31.883441+00:00
-- url     : https://prove2.me/submissions/564e1b69-444d-44ec-b78a-bbf486233c1a

import Definitions.Def_KLSModular_BrownianMotion_Gaussian_BrownianMotion
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ProbabilityTheory MeasureTheory NNReal
open scoped NNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : ℝ≥0 → Ω → ℝ) (h : IsPreBrownianReal X P) (t : ℝ≥0) :
    Measurable (h.mk X t) := by
  exact h.exists_continuous_modification.choose_spec.1 t
