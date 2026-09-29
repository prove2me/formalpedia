-- Prove2me | solution 1 for OddPerfectNumber.s3_29_not_dvd_59sq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-19T21:13:51.784546+00:00
-- url     : https://prove2.me/submissions/e953f44e-2da5-435a-98cc-b38293f37ff0

import Mathlib

theorem solution :
    ¬ 59 ^ 2 ∣ ∑ i ∈ Finset.range 29, 3 ^ i :=
  by decide
