-- Prove2me | solution 1 for ShiQMACenteredGap.fractionBits_numerator
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-10-01T12:09:55.832766+00:00
-- url     : https://prove2.me/submissions/8ff31825-4494-483f-831e-a023c2247020

import Definitions.Def_ShiQMACenteredGapComputableCoin
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

open ShiQMACenteredGap

theorem solution (k j : Nat) (hj : j < 2 ^ k) :
    binaryNumerator (fractionBits k j) = j := by
  induction k generalizing j with
  | zero =>
    have hj0 : j = 0 := by simpa using hj
    subst j
    rfl
  | succ k ih =>
    have hpos : 0 < (2 : Nat) ^ k := pow_pos (by decide) _
    have hrec := ih (j % 2 ^ k) (Nat.mod_lt _ hpos)
    simp only [fractionBits, binaryNumerator, fractionBits_length, hrec]
    by_cases h : 2 ^ k ≤ j
    · simp only [h, decide_true, ↓reduceIte]
      have hj' : j < 2 ^ k * 2 := by simpa only [pow_succ] using hj
      have hsub : j - 2 ^ k < 2 ^ k := by omega
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt hsub]
      omega
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, zero_add]
      exact Nat.mod_eq_of_lt (by omega)
