-- Prove2me | solution 1 for RogersSatchell.Unbiased.expected_estimator_eq
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T12:26:22.953048+00:00
-- url     : https://prove2.me/submissions/03ebf8e6-c9b7-406c-9aa8-2d0cea3fcf0a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RogersSatchell_Unbiased_Process
import Theorems.Thm_RogersSatchell_Unbiased_max_term_mean
import Theorems.Thm_RogersSatchell_Unbiased_min_term_mean

open MeasureTheory ProbabilityTheory NNReal
open RogersSatchell.Unbiased

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hcont : ∀ ω, Continuous fun t => B t ω)
    (c σ : ℝ) (hσ : 0 ≤ σ) (t : ℝ≥0) :
    Integrable (fun ω => runMax σ c B t ω * (runMax σ c B t ω - logPrice σ c B t ω)
      + runMin σ c B t ω * (runMin σ c B t ω - logPrice σ c B t ω)) P ∧
    ∫ ω, (runMax σ c B t ω * (runMax σ c B t ω - logPrice σ c B t ω)
      + runMin σ c B t ω * (runMin σ c B t ω - logPrice σ c B t ω)) ∂P = σ ^ 2 * t := by
  obtain ⟨h1, e1⟩ := max_term_mean hB hcont c σ hσ t
  obtain ⟨h2, e2⟩ := min_term_mean hB hcont c σ hσ t
  refine ⟨h1.add h2, ?_⟩
  rw [integral_add h1 h2, e1, e2]
  ring
