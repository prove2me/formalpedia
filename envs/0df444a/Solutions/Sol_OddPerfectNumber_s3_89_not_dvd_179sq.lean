-- Prove2me | solution 1 for OddPerfectNumber.s3_89_not_dvd_179sq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-19T21:14:14.227901+00:00
-- url     : https://prove2.me/submissions/afc17263-e51e-4f98-86bb-3f9d5e49c30a

import Mathlib

theorem solution :
    ¬ 179 ^ 2 ∣ ∑ i ∈ Finset.range 89, 3 ^ i :=
  by decide
