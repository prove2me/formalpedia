-- Prove2me | solution 1 for OddPerfectNumber.s3_83_not_dvd_167sq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-19T21:14:09.982368+00:00
-- url     : https://prove2.me/submissions/ea06be2a-a7fa-4004-b8e3-3dc4c3a860bc

import Mathlib

theorem solution :
    ¬ 167 ^ 2 ∣ ∑ i ∈ Finset.range 83, 3 ^ i :=
  by decide
