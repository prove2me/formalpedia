-- Prove2me | solution 1 for SeatInventory.Gaussian.tail_antitone
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T11:26:08.697168+00:00
-- url     : https://prove2.me/submissions/527b95db-7bd1-48ec-9c36-240ad544ed24

import Mathlib
import Definitions.Def_SeatInventory_Gaussian_Model

open MeasureTheory ProbabilityTheory

open MeasureTheory ProbabilityTheory SeatInventory.Gaussian in
theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ) (hf : 0 ≤ f) :
    Antitone (tailProb μ) ∧ Antitone (emsr μ f) := by
  have h1 : Antitone (tailProb μ) := by
    intro a b hab
    unfold tailProb
    exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (Set.Ici_subset_Ici.mpr hab))
  refine ⟨h1, ?_⟩
  intro a b hab
  unfold emsr
  exact mul_le_mul_of_nonneg_right (h1 hab) hf
