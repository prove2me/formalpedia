-- Prove2me | solution 1 for VariableBound.Rename.steps_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:19:25.584469+00:00
-- url     : https://prove2.me/submissions/975e63fb-d6bb-4ba1-a653-c25bcac1442c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Definitions.Def_VariableBound_Paper_Rename_Time

set_option autoImplicit false
section
section
open VariableBound VariableBound.Rename
namespace VariableBound.Rename
theorem _root_.solution (q a b E : ℕ) : q * (a + 2 ^ E + 1) ^ q ≤ q * 2 ^ q * (a + 1) ^ q + 2 * q * (b + 2 ^ E + 1) ^ (2 * q) := by
  have h1 : (a + 2 ^ E + 1) ^ q ≤ 2 ^ q * (a + 1) ^ q + 2 ^ q * (2 ^ E) ^ q := by
    rcases le_total (a + 1) (2 ^ E) with h | h
    · calc (a + 2 ^ E + 1) ^ q ≤ (2 * 2 ^ E) ^ q := Nat.pow_le_pow_left (by omega) q
        _ = 2 ^ q * (2 ^ E) ^ q := mul_pow _ _ _
        _ ≤ _ := Nat.le_add_left _ _
    · calc (a + 2 ^ E + 1) ^ q ≤ (2 * (a + 1)) ^ q := Nat.pow_le_pow_left (by omega) q
        _ = 2 ^ q * (a + 1) ^ q := mul_pow _ _ _
        _ ≤ _ := Nat.le_add_right _ _
  have h2 : 2 ^ q * (2 ^ E) ^ q ≤ (b + 2 ^ E + 1) ^ (2 * q) := by
    rw [two_mul, pow_add]
    have hE : 1 ≤ 2 ^ E := Nat.one_le_two_pow
    exact Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) q) (Nat.pow_le_pow_left (by omega) q)
  calc q * (a + 2 ^ E + 1) ^ q ≤ q * (2 ^ q * (a + 1) ^ q + (b + 2 ^ E + 1) ^ (2 * q)) := Nat.mul_le_mul_left _ (h1.trans (Nat.add_le_add_left h2 _))
    _ = q * 2 ^ q * (a + 1) ^ q + q * (b + 2 ^ E + 1) ^ (2 * q) := by ring
    _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
end VariableBound.Rename
