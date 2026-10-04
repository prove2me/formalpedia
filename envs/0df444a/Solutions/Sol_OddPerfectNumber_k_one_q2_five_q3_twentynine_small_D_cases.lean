-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_small_D_cases
-- status  : ACCEPTED   (disprove)
-- author  : @Patrick
-- created : 2026-09-18T00:54:57.838155+00:00
-- url     : https://prove2.me/submissions/2183166c-280e-48fb-a4ca-a017a655faeb

import Mathlib.Data.Nat.Prime.Basic

theorem solution : ¬ (∀ (D p q4 : Nat), (D < 75) → (Odd D) → p.Prime →
    (p = 2 * D - 1) → (29 < q4) → (D < q4) →
    (∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 29 ∨ r = q4) →
    D = 27 ∨ D = 31 ∨ D = 37 ∨ D = 45) := by
  intro h
  have hs : ∀ r : ℕ, r.Prime → r ∣ 3 → r = 3 ∨ r = 5 ∨ r = 29 ∨ r = 31 := by
    intro r hr hd
    exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr (by decide)).mp hd)
  have hc := h 3 5 31 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) hs
  exact (by decide : ¬ (3 = 27 ∨ 3 = 31 ∨ 3 = 37 ∨ 3 = 45)) hc

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
