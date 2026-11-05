-- Prove2me | solution 1 for VariableBound.Rename.poly_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:20:38.711202+00:00
-- url     : https://prove2.me/submissions/a66c1f3b-773c-4c04-b86b-2f3b249472c7

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
theorem _root_.solution (q : ℕ) {a : ℕ} (ha : 1 ≤ a) : q * 2 ^ q * (a + 1) ^ q ≤ q * 4 ^ q * a ^ (q * 4 ^ q) := by
  have h1 : (a + 1) ^ q ≤ 2 ^ q * a ^ q := by
    rw [← mul_pow]
    exact Nat.pow_le_pow_left (by omega) q
  have h2 : a ^ q ≤ a ^ (q * 4 ^ q) := Nat.pow_le_pow_right ha (Nat.le_mul_of_pos_right _ (by positivity))
  calc q * 2 ^ q * (a + 1) ^ q ≤ q * 2 ^ q * (2 ^ q * a ^ (q * 4 ^ q)) := Nat.mul_le_mul_left _ (h1.trans (Nat.mul_le_mul_left _ h2))
    _ = q * (2 * 2) ^ q * a ^ (q * 4 ^ q) := by rw [mul_pow]; ring
    _ = _ := by norm_num
end VariableBound.Rename
