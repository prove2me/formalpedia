-- Prove2me | solution 1 for OddPerfectNumber.s3_131_not_dvd_263sq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-19T21:18:57.193388+00:00
-- url     : https://prove2.me/submissions/b80f2da2-0408-4f13-82a7-11a61255e2f9

import Mathlib

set_option maxRecDepth 200000 in
theorem solution :
    ¬ 263 ^ 2 ∣ ∑ i ∈ Finset.range 131, 3 ^ i :=
  by decide
