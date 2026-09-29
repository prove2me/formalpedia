-- Prove2me | solution 1 for OddPerfectNumber.s3_113_not_dvd_227sq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-19T21:14:19.135425+00:00
-- url     : https://prove2.me/submissions/89f0d0f9-dade-4046-a3cd-c0470d065818

import Mathlib

theorem solution :
    ¬ 227 ^ 2 ∣ ∑ i ∈ Finset.range 113, 3 ^ i :=
  by decide
