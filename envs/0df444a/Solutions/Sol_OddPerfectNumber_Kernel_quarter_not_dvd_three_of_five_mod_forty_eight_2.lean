-- Prove2me | solution 2 for OddPerfectNumber.Kernel.quarter_not_dvd_three_of_five_mod_forty_eight
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T23:27:58.371259+00:00
-- url     : https://prove2.me/submissions/caf32250-3bdf-4878-bca9-a95148765ead

import Mathlib

theorem solution (p : Nat)
    (h48 : p % 48 = 5) :
    Not (Dvd.dvd 3 ((p - 1) / 4)) := by
  obtain ⟨k, hk⟩ : ∃ k, p = 48 * k + 5 := ⟨p / 48, by omega⟩
  have hq : (p - 1) / 4 = 12 * k + 1 := by omega
  intro hd
  rw [hq] at hd
  omega
