-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P92.bob_pairing_penalty
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T18:53:16.906556+00:00
-- url     : https://prove2.me/submissions/7611701e-e872-4a86-9c91-d9c13ccc542a

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P92

open scoped Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Intake100.P92 in
theorem solution (P : Bool × Bool → ℝ)
    (hP : (∀ x, 0 ≤ P x) ∧ ∑ x, P x = 1)
    (hbalanced : (∀ a, ∑ b, P (a,b) = 1/2) ∧ (∀ b, ∑ a, P (a,b) = 1/2))
    (mu Q ca cb : ℝ)
    (hmu : 0 ≤ mu) (hQ : Q ∈ Set.Icc (0:ℝ) 1) :
    (∑ x, bobPairLaw P (x,true)) = 1/2 ∧
    (∀ x, bobPairLaw P (x,true) / (∑ y, bobPairLaw P (y,true)) = P x) ∧
    dw (mu/4) Q ca cb = dw (mu/2) Q ca cb / 2 := by
  have hb : ∀ x, bobPairLaw P (x, true) = P x / 2 := fun x => rfl
  have h1 : (∑ x, bobPairLaw P (x,true)) = 1/2 := by
    simp only [hb]
    rw [← Finset.sum_div, hP.2]
  refine ⟨h1, fun x => ?_, ?_⟩
  · rw [h1, hb]
    ring
  · simp only [dw]
    ring
