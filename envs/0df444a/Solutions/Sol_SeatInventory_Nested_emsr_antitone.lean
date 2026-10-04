-- Prove2me | solution 1 for SeatInventory.Nested.emsr_antitone
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T11:09:16.95875+00:00
-- url     : https://prove2.me/submissions/5adfbf59-9f1c-4f3a-af5f-d204ad0a6360

import Mathlib
import Definitions.Def_SeatInventory_Nested_Model

open MeasureTheory SeatInventory.Nested in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (r : Ω → ℕ) (f : ℝ) (hf : 0 ≤ f) :
    Antitone (tailProb μ r) ∧ Antitone (emsr μ r f) := by
  have h1 : Antitone (tailProb μ r) := by
    intro a b hab
    unfold tailProb
    exact measureReal_mono (fun ω (hω : b ≤ r ω) => le_trans hab hω)
  refine ⟨h1, ?_⟩
  intro a b hab
  unfold emsr
  exact mul_le_mul_of_nonneg_left (h1 hab) hf
