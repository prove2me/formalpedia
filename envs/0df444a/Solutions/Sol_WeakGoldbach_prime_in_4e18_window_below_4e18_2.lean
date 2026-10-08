-- Prove2me | solution 2 for WeakGoldbach.prime_in_4e18_window_below_4e18
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T20:50:09.616131+00:00
-- url     : https://prove2.me/submissions/7102591f-a697-49b3-b4fc-980deb86e3d5

import Mathlib.NumberTheory.Bertrand

set_option autoImplicit false

theorem solution (x : ℕ) (hx : x ≤ 4 * 10 ^ 18) :
    ∃ p : ℕ, x < p ∧ p < x + 4 * 10 ^ 18 ∧ Nat.Prime p := by
  rcases eq_or_ne x 0 with rfl | hx0
  · refine ⟨2, by decide, by decide, Nat.prime_two⟩
  · obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul x hx0
    refine ⟨p, hlt, ?_, hp⟩
    rcases eq_or_lt_of_le hx with heq | hxlt
    · rw [heq] at hle ⊢
      exact Nat.lt_of_le_of_ne hle fun hpe => by
        rw [hpe] at hp
        have heven : 2 ∣ 8 * 10 ^ 18 := ⟨4 * 10 ^ 18, by ring⟩
        exact absurd hp (Nat.not_prime_of_dvd_of_lt heven (by norm_num) (by norm_num))
    · have h2lt : 2 * x < x + 4 * 10 ^ 18 := by
        have := Nat.add_lt_add_left hxlt x
        simpa [two_mul] using this
      exact lt_of_le_of_lt hle h2lt

#print axioms solution
