-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P47.accepted_settings_agree
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:03:50.455962+00:00
-- url     : https://prove2.me/submissions/ef5135c9-2f43-4405-a309-a46a0b91957a

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P47

open scoped ComplexConjugate

open scoped BigOperators

open QAlgorithms.Papers.Independent.Intakethird100.P47 in
theorem solution (p : Behavior) (w : PairLaw)
    (hp : IsBehavior p) (hw : IsPairLaw w)
    (h10 : p true false false false = 0) (h01 : p false true false false = 0)
    (hs : 0 < siftingProbability p w) :
    (∀ A B, A ≠ B → acceptedMass p w A B = 0) ∧
    (∑ A, ∑ B, if A = B then acceptedLaw p w A B else 0) = 1 := by
  have h1 : ∀ A B, A ≠ B → acceptedMass p w A B = 0 := by
    intro A B hAB
    cases A <;> cases B
    · exact absurd rfl hAB
    · simp only [acceptedMass, h01, mul_zero]
    · simp only [acceptedMass, h10, mul_zero]
    · exact absurd rfl hAB
  refine ⟨h1, ?_⟩
  have hS : siftingProbability p w = acceptedMass p w true true + acceptedMass p w false false := by
    unfold siftingProbability
    simp only [Fintype.sum_bool]
    rw [h1 true false (by decide), h1 false true (by decide)]
    ring
  have e : (∑ A, ∑ B, if A = B then acceptedLaw p w A B else 0) =
      acceptedLaw p w true true + acceptedLaw p w false false := by
    simp only [Fintype.sum_bool]
    simp
  rw [e]
  unfold acceptedLaw
  rw [← add_div, ← hS, div_self hs.ne']
