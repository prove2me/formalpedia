-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.bijunctive_output_predicate_event_measurable
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:51:44.458195+00:00
-- url     : https://prove2.me/submissions/e08daaf2-35d5-4acb-b85e-a72f623f2cee

import Theorems.Thm_StabilityDichotomies_Bijunctive_bijunctive_output_event_measurable
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem solution {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (ε : ℝ) (P : (V → Bool) → Prop) :
    MeasurableSet {s : (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ) |
      P (bijunctiveOutput rep I ε s.1 s.2.1 s.2.2)} := by
  classical
  have heq : {s : (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ) |
      P (bijunctiveOutput rep I ε s.1 s.2.1 s.2.2)} =
      ⋃ x : V → Bool, if P x then {s | bijunctiveOutput rep I ε s.1 s.2.1 s.2.2 = x} else ∅ := by
    ext s
    simp only [mem_setOf_eq, mem_iUnion]
    constructor
    · intro h
      refine ⟨bijunctiveOutput rep I ε s.1 s.2.1 s.2.2, ?_⟩
      simp [h]
    · rintro ⟨x,hx⟩
      by_cases hPx : P x
      · have hx' : bijunctiveOutput rep I ε s.1 s.2.1 s.2.2 = x := by simpa [hPx] using hx
        simpa [hx'] using hPx
      · simp [hPx] at hx
  rw [heq]
  apply MeasurableSet.iUnion
  intro x
  split_ifs
  · exact bijunctive_output_event_measurable rep I ε x
  · exact MeasurableSet.empty
