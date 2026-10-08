-- Prove2me | solution 1 for OddPerfectNumber.Kernel.middle_source_exponent_forces_square_support
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T17:36:55.279292+00:00
-- url     : https://prove2.me/submissions/0d30a3a7-29c1-4457-bc3a-e8d08bef25f8

import Mathlib

theorem solution (p m q a b d1 u r : Nat)
    (hq : q.Prime)
    (hm : m = 3 * u * a * b * d1 * q * r)
    (he : 2 ≤ m.factorization q)
    (h3 : ¬ q ∣ 3) (hu : ¬ q ∣ u) (hb : ¬ q ∣ b)
    (hd : ¬ q ∣ d1) (hr : ¬ q ∣ r) :
    q ∣ a := by
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0] at he
    simp at he
  have h2 : q ^ 2 ∣ m := (hq.pow_dvd_iff_le_factorization hm0).mpr he
  have hX : m = q * (3 * u * a * b * d1 * r) := by rw [hm]; ring
  rw [hX, pow_two] at h2
  have hqX : q ∣ 3 * u * a * b * d1 * r :=
    Nat.dvd_of_mul_dvd_mul_left hq.pos h2
  rcases hq.dvd_mul.mp hqX with h | h
  · rcases hq.dvd_mul.mp h with h | h
    · rcases hq.dvd_mul.mp h with h | h
      · rcases hq.dvd_mul.mp h with h | h
        · rcases hq.dvd_mul.mp h with h | h
          · exact absurd h h3
          · exact absurd h hu
        · exact h
      · exact absurd h hb
    · exact absurd h hd
  · exact absurd h hr
