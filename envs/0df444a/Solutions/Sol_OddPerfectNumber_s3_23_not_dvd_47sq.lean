-- Prove2me | solution 1 for OddPerfectNumber.s3_23_not_dvd_47sq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-19T21:13:47.036659+00:00
-- url     : https://prove2.me/submissions/db498284-d4bc-4c17-a19d-057380a12ee4

import Mathlib

theorem solution :
    ¬ 47 ^ 2 ∣ ∑ i ∈ Finset.range 23, 3 ^ i :=
  by decide
