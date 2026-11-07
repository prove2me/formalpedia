-- Prove2me | solution 1 for RogersSatchell.Unbiased.min_term_mean
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T12:26:22.199353+00:00
-- url     : https://prove2.me/submissions/8b37a2e5-81a6-4c93-9a00-6dadf0454528
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RogersSatchell_Unbiased_Process
import Theorems.Thm_RogersSatchell_Unbiased_max_term_mean

open MeasureTheory ProbabilityTheory NNReal
open RogersSatchell.Unbiased

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hcont : ∀ ω, Continuous fun t => B t ω)
    (c σ : ℝ) (hσ : 0 ≤ σ) (t : ℝ≥0) :
    Integrable (fun ω => runMin σ c B t ω * (runMin σ c B t ω - logPrice σ c B t ω)) P ∧
    ∫ ω, runMin σ c B t ω * (runMin σ c B t ω - logPrice σ c B t ω) ∂P = σ ^ 2 * t / 2 := by
  have hcont' : ∀ ω, Continuous fun t => (-B) t ω := fun ω => by
    exact (hcont ω).neg
  have hlog : ∀ u ω, logPrice σ (-c) (-B) u ω = - logPrice σ c B u ω := by
    intro u ω; simp only [logPrice, Pi.neg_apply]; ring
  have hmin : ∀ ω, runMin σ c B t ω = - runMax σ (-c) (-B) t ω := by
    intro ω
    have : (fun u => logPrice σ c B u ω) '' Set.Icc 0 t
        = - ((fun u => logPrice σ (-c) (-B) u ω) '' Set.Icc 0 t) := by
      rw [← Set.image_neg_eq_neg, Set.image_image]
      simp only [hlog, neg_neg]
    rw [runMin, runMax, this, Real.sInf_neg]
  have key : ∀ ω, runMin σ c B t ω * (runMin σ c B t ω - logPrice σ c B t ω)
      = runMax σ (-c) (-B) t ω * (runMax σ (-c) (-B) t ω - logPrice σ (-c) (-B) t ω) := by
    intro ω; rw [hmin, hlog]; ring
  obtain ⟨h1, e1⟩ := max_term_mean hB.neg hcont' (-c) σ hσ t
  simp_rw [key]
  exact ⟨h1, e1⟩
