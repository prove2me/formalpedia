-- Prove2me | solution 1 for OddPerfectNumber.s3_53_not_dvd_107sq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-19T21:14:00.452843+00:00
-- url     : https://prove2.me/submissions/dfe7ff16-ff55-4799-b8f4-89aee63621a6

import Mathlib

theorem solution :
    ¬ 107 ^ 2 ∣ ∑ i ∈ Finset.range 53, 3 ^ i :=
  by decide
