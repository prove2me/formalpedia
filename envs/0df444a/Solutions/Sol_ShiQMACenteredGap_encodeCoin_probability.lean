-- Prove2me | solution 1 for ShiQMACenteredGap.encodeCoin_probability
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-10-01T12:23:02.520757+00:00
-- url     : https://prove2.me/submissions/80ab34a5-369e-4dbb-9593-40e48862bad6

import Definitions.Def_ShiQMACenteredGapComputableCoin
import Theorems.Thm_ShiQMACenteredGap_fractionBits_numerator
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

open ShiQMACenteredGap

theorem solution (k j : Nat) (hj : j ≤ 2 ^ k) :
    (encodeCoin k j).probability = (j : ℝ) / (2 : ℝ) ^ k := by
  by_cases h : j = 2 ^ k
  · subst j
    simp [encodeCoin, CoinCode.probability]
  · simp [encodeCoin, h, CoinCode.probability, dyadicValue,
      fractionBits_length, fractionBits_numerator k j (by omega)]
