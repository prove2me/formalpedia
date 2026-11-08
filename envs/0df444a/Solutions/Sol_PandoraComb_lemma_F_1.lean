-- Prove2me | solution 1 for PandoraComb.lemma_F_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:28:14.161634+00:00
-- url     : https://prove2.me/submissions/a99fbd83-f9fd-4a88-b631-f105486da7d1

import Mathlib

open MeasureTheory Filter Topology

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (h0 : μ (Set.Iio 0) = 0)
    (hint : Integrable (fun x : ℝ => x) μ) :
    Tendsto (fun κ : ℝ => ∫ x, max (x - κ) 0 ∂μ) atTop (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := atTop)
    (F := fun κ x => max (x - κ) 0) (f := fun _ => (0:ℝ)) (fun x => |x|)
    (Eventually.of_forall (fun κ =>
      ((continuous_id.sub continuous_const).max continuous_const).aestronglyMeasurable))
    (eventually_atTop.2 ⟨0, fun κ hκ => Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [le_abs_self x]) (abs_nonneg x))⟩)
    hint.abs
    (Eventually.of_forall (fun x => tendsto_const_nhds.congr'
      ((eventually_ge_atTop x).mono (fun κ hκ => (max_eq_right (by linarith)).symm))))
  simpa using h
