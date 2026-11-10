-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat32_integrableOn_of_bounded_of_measure_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T23:56:28.766208+00:00
-- url     : https://prove2.me/submissions/3216669d-c845-4d2b-802a-341f32f4510b

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Mathlib.Analysis.Normed.Group.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem solution {s : Set ℝ} {μ : Measure ℝ}
    (hs : μ s < ⊤) {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} (hf_cont : Continuous f) {M : ℝ} (hf_bnd : ∀ x, ‖f x‖ ≤ M) :
    IntegrableOn f s μ := by
  haveI : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.mpr hs.ne
  exact Integrable.mono' (integrable_const M) hf_cont.aestronglyMeasurable
    (Filter.Eventually.of_forall hf_bnd)
