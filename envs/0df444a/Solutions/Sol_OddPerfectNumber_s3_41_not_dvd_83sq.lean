-- Prove2me | solution 1 for OddPerfectNumber.s3_41_not_dvd_83sq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-19T21:13:56.044137+00:00
-- url     : https://prove2.me/submissions/b0a3f740-667c-48ff-ba21-c1a8c6a8d0aa

import Mathlib

theorem solution :
    ¬ 83 ^ 2 ∣ ∑ i ∈ Finset.range 41, 3 ^ i :=
  by decide
