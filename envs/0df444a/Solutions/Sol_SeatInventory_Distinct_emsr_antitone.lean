-- Prove2me | solution 1 for SeatInventory.Distinct.emsr_antitone
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T12:28:08.287715+00:00
-- url     : https://prove2.me/submissions/c233961d-e998-460a-9c32-ef4864949414

import Definitions.Def_SeatInventory_Distinct_DemandModel

open MeasureTheory SeatInventory.Distinct

private theorem tailProb_antitone_aux (p : PMF ℕ) :
    ∀ S T : ℕ, S ≤ T → tailProb p T ≤ tailProb p S := by
  intro S T hST
  have hsub : Set.Ici T ⊆ Set.Ici S := Set.Ici_subset_Ici.mpr hST
  have hmeas : MeasurableSet (Set.Ici S) := (Set.to_countable _).measurableSet
  have hmeasT : MeasurableSet (Set.Ici T) := (Set.to_countable _).measurableSet
  have h1 : tailProb p S = (p.toMeasure (Set.Ici S)).toReal := by
    rw [tailProb, p.toMeasure_apply_eq_toOuterMeasure_apply hmeas]
  have h2 : tailProb p T = (p.toMeasure (Set.Ici T)).toReal := by
    rw [tailProb, p.toMeasure_apply_eq_toOuterMeasure_apply hmeasT]
  rw [h1, h2]
  exact ENNReal.toReal_mono (measure_ne_top p.toMeasure (Set.Ici S)) (p.toMeasure.mono hsub)

theorem solution (f : ℝ) (hf : 0 ≤ f) (p : PMF ℕ) :
    Antitone (tailProb p) ∧ Antitone (emsr f p) := by
  refine ⟨fun a b hab => tailProb_antitone_aux p a b hab, ?_⟩
  intro a b hab
  unfold emsr
  exact mul_le_mul_of_nonneg_left (tailProb_antitone_aux p a b hab) hf
