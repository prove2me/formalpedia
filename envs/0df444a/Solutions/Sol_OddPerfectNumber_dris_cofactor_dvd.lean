-- Prove2me | solution 1 for OddPerfectNumber.dris_cofactor_dvd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T09:18:35.367264+00:00
-- url     : https://prove2.me/submissions/0d094ee5-7820-42e7-9b29-a297eeb48890

import Mathlib

-- STAGED direct proof of the shared Dris packaging lemma. Every lemma name
-- verified against pinned Mathlib: Nat.coprime_two_right
-- (Data/Nat/Prime/Basic.lean), Nat.Coprime.dvd_of_dvd_mul_left (used in
-- Data/Nat/GCD/Basic.lean).
theorem solution (m s t : Nat)
    (hs_odd : Odd s)
    (hpack : 2 * m ^ 2 = t * s) :
    s ∣ m ^ 2 := by
  have hcop : Nat.Coprime s 2 := Nat.coprime_two_right.mpr hs_odd
  have hdvd : s ∣ 2 * m ^ 2 := by
    rw [hpack]
    exact dvd_mul_left s t
  exact hcop.dvd_of_dvd_mul_left hdvd
