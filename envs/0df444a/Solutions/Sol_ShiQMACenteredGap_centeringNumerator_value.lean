-- Prove2me | solution 1 for ShiQMACenteredGap.centeringNumerator_value
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-10-01T11:25:09.684976+00:00
-- url     : https://prove2.me/submissions/5f935c51-ae58-4511-a0ea-0bc6e596b2ca

import Definitions.Def_ShiQMACenteredGapComputableCoin
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

open ShiQMACenteredGap

theorem solution (k A B : Nat) (hA : A ≤ 2 ^ k) (hB : B ≤ 2 ^ k) :
    (centeringNumerator k A B : ℝ) / (2 : ℝ) ^ (k + 1) =
      1 - ((A : ℝ) / (2 : ℝ) ^ k + (B : ℝ) / (2 : ℝ) ^ k) / 2 := by
  have hab : A + B ≤ 2 ^ (k + 1) := by rw [pow_succ]; omega
  have hn : (centeringNumerator k A B : ℝ) = (2 : ℝ) ^ (k + 1) - ((A : ℝ) + B) := by
    simp only [centeringNumerator, Nat.cast_sub hab, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add]
  rw [hn, pow_succ]
  field_simp
  <;> ring
