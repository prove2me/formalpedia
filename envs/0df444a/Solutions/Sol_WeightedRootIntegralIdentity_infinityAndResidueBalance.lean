-- Prove2me | solution 1 for WeightedRootIntegralIdentity.infinityAndResidueBalance
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-20T11:01:05.295457+00:00
-- url     : https://prove2.me/submissions/e54fa05b-6ce5-451b-987d-5dea0190e0ec

import Mathlib

theorem solution
    (J S P d p : ℝ)
    (hbalance : J = -d + p)
    (hd : d = -S)
    (hp : p = -P) :
    J = S - P := by
  rw [hd, hp] at hbalance
  linarith
