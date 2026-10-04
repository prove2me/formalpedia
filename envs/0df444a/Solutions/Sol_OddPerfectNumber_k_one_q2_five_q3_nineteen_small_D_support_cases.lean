-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_small_D_support_cases
-- status  : ACCEPTED   (disprove)
-- author  : @Patrick
-- created : 2026-09-18T01:25:31.925581+00:00
-- url     : https://prove2.me/submissions/2835f9df-8695-41b8-bcf5-a7f7f89a99a6

import Mathlib.Data.Nat.Prime.Basic

theorem solution : ¬ (∀ (D p q4 : Nat), (D < 225) → (Odd D) → p.Prime →
    (p = 2 * D - 1) → (19 < q4) →
    (∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 19 ∨ r = q4) →
    D = 3 ∨ D = 9 ∨ D = 15 ∨ D = 19 ∨ D = 27 ∨ D = 45 ∨ D = 57 ∨
      D = 75 ∨ D = 135) := by
  intro h
  have hs : ∀ r : ℕ, r.Prime → r ∣ 31 → r = 3 ∨ r = 5 ∨ r = 19 ∨ r = 31 := by
    intro r hr hd
    exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hr (by decide)).mp hd)))
  have hc := h 31 61 31 (by decide) (by decide) (by decide) (by decide) (by decide) hs
  exact (by decide : ¬ (31 = 3 ∨ 31 = 9 ∨ 31 = 15 ∨ 31 = 19 ∨ 31 = 27 ∨
    31 = 45 ∨ 31 = 57 ∨ 31 = 75 ∨ 31 = 135)) hc

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
