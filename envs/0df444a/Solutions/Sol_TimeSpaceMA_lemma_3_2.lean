-- Prove2me | solution 1 for TimeSpaceMA.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:38:09.211606+00:00
-- url     : https://prove2.me/submissions/e83e6dcc-dd84-48a9-b677-3f550d7b2862

import Definitions.Def_TimeSpaceMA_lambdaForm

open TimeSpaceMA in
theorem solution (w₁ w₂ z : ℤ) :
    0 ≤ gammaForm w₁ w₂ z ∧
      (gammaForm w₁ w₂ z = 0 ↔ (w₁ = 0 ∨ w₁ = 1) ∧ (w₂ = 0 ∨ w₂ = 1) ∧ z = 1 - w₁ * w₂) := by
  have hb : ∀ w : ℤ, 0 ≤ w * (w - 1) := by
    intro w
    rcases le_or_gt w 0 with h | h
    · exact mul_nonneg_of_nonpos_of_nonpos h (by linarith)
    · exact mul_nonneg (by linarith) (by linarith)
  have hb0 : ∀ w : ℤ, w * (w - 1) = 0 ↔ w = 0 ∨ w = 1 := by
    intro w
    rw [mul_eq_zero, sub_eq_zero]
  unfold gammaForm bForm
  refine ⟨by linarith [hb w₁, hb w₂, hb (w₁ + w₂ + 2 * z - 2)], ?_⟩
  constructor
  · intro h
    have e1 : w₁ * (w₁ - 1) = 0 := by linarith [hb w₁, hb w₂, hb (w₁ + w₂ + 2 * z - 2)]
    have e2 : w₂ * (w₂ - 1) = 0 := by linarith [hb w₁, hb w₂, hb (w₁ + w₂ + 2 * z - 2)]
    have e3 : (w₁ + w₂ + 2 * z - 2) * (w₁ + w₂ + 2 * z - 2 - 1) = 0 := by
      linarith [hb w₁, hb w₂, hb (w₁ + w₂ + 2 * z - 2)]
    have r1 := (hb0 _).1 e1
    have r2 := (hb0 _).1 e2
    have r3 := (hb0 _).1 e3
    refine ⟨r1, r2, ?_⟩
    rcases r1 with h1 | h1 <;> rcases r2 with h2 | h2 <;> subst h1 <;> subst h2 <;> omega
  · rintro ⟨h1 | h1, h2 | h2, h3⟩ <;> subst h1 <;> subst h2 <;> subst h3 <;> norm_num
