-- Prove2me | solution 1 for OddPerfectNumber.k_one_half_successor_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T11:03:57.7843+00:00
-- url     : https://prove2.me/submissions/0a6e396f-bb0f-4f3c-b353-f0e4e5dba39d

import Mathlib

theorem solution (p m d q : Nat)
    (hq : q.Prime)
    (hdvd : m ^ 2 = ((p + 1) / 2) * d)
    (hqD : q ∣ (p + 1) / 2) :
    q ∣ m := by
  apply hq.dvd_of_dvd_pow
  rw [hdvd]
  exact dvd_mul_of_dvd_left hqD d
