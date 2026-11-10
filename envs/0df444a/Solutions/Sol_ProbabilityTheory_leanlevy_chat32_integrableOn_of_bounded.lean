-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat32_integrableOn_of_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T23:56:32.020749+00:00
-- url     : https://prove2.me/submissions/95454cdb-1079-4f59-a389-51c043963487

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Mathlib.Analysis.Normed.Group.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem solution {s : Set ℝ} {μ : Measure ℝ} [IsFiniteMeasure μ]
    {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} (hf_cont : Continuous f) {M : ℝ} (hf_bnd : ∀ x, ‖f x‖ ≤ M) :
    IntegrableOn f s μ := by
  exact Integrable.mono' (integrable_const M) hf_cont.aestronglyMeasurable
    (Filter.Eventually.of_forall hf_bnd) |>.integrableOn
