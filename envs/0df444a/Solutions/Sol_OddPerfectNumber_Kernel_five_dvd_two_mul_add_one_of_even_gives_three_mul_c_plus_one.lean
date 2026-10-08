-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_dvd_two_mul_add_one_of_even_gives_three_mul_c_plus_one
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T05:24:03.016564+00:00
-- url     : https://prove2.me/submissions/c511ae1a-d1da-439a-b7b2-5bb439c0e2ed

import Mathlib

theorem cex_0ba14d89 : ¬ (∀ (a c : Nat), Even a → Dvd.dvd 5 (a + 2 * c + 1) →
    Dvd.dvd 5 (3 * c + a + 1)) := by
  intro h
  have := h 0 2 (by decide) (by decide)
  omega

theorem solution : ¬ (∀ (a c : Nat), Even a → Dvd.dvd 5 (a + 2 * c + 1) →
    Dvd.dvd 5 (3 * c + a + 1)) := by
  exact cex_0ba14d89

