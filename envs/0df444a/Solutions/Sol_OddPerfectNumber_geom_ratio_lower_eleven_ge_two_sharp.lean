-- Prove2me | solution 1 for OddPerfectNumber.geom_ratio_lower_eleven_ge_two_sharp
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T19:32:32.853502+00:00
-- url     : https://prove2.me/submissions/d9ce52a4-260d-44d3-9525-8d8369f50aa5

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_eleven_ge_two_sharp_v3

open OddPerfectNumber

theorem solution (n : Nat) (hn : 2 ≤ n) :
    133 * 11 ^ n ≤ 121 * (∑ i ∈ Finset.range (n + 1), 11 ^ i) :=
  OddPerfectNumber.geom_ratio_lower_eleven_ge_two_sharp_v3 n hn
