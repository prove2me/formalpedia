-- Prove2me | solution 1 for PaddedDescent.overhead_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:27:57.862139+00:00
-- url     : https://prove2.me/submissions/e0f473e1-e2de-4fa0-915a-55cd46b31b46

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Choice
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_PaddedDescent_Threshold
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_PaddedDescent_Ytop_lower
import Theorems.Thm_PaddedDescent_Ytop_pos


set_option autoImplicit false
section
section
open PaddedDescent
namespace PaddedDescent
theorem _root_.solution {s n W a c : ℕ} (hc : c ≤ 2 ^ 500) (hn : Ytop s ^ (2 * a + 2) ≤ n)
    (hW : W ≤ c * Ytop s ^ a * (Nat.sqrt n + 1)) : W * 2 ^ s ≤ n := by
  have hY : 2 ^ (52 * s + 694) ≤ Ytop s := Ytop_lower s
  have hY1 : 0 < Ytop s := Ytop_pos s
  have hq : Ytop s ^ (a + 1) ≤ Nat.sqrt n := by
    rw [Nat.le_sqrt, ← pow_add]
    exact le_trans (le_of_eq (by congr 1; ring)) hn
  have hq1 : 1 ≤ Nat.sqrt n := le_trans (Nat.one_le_pow _ _ hY1) hq
  have hcs : 2 * c * 2 ^ s ≤ Ytop s := by
    calc 2 * c * 2 ^ s ≤ 2 * 2 ^ 500 * 2 ^ s := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hc)
      _ = 2 ^ (1 + 500 + s) := by rw [pow_add, pow_add, pow_one]
      _ ≤ 2 ^ (52 * s + 694) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ Ytop s := hY
  calc W * 2 ^ s ≤ c * Ytop s ^ a * (Nat.sqrt n + 1) * 2 ^ s := Nat.mul_le_mul_right _ hW
    _ ≤ c * Ytop s ^ a * (2 * Nat.sqrt n) * 2 ^ s :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
    _ = 2 * c * 2 ^ s * (Ytop s ^ a * Nat.sqrt n) := by ring
    _ ≤ Ytop s * (Ytop s ^ a * Nat.sqrt n) := Nat.mul_le_mul_right _ hcs
    _ = Ytop s ^ (a + 1) * Nat.sqrt n := by ring
    _ ≤ Nat.sqrt n * Nat.sqrt n := Nat.mul_le_mul_right _ hq
    _ ≤ n := Nat.sqrt_le n
end PaddedDescent
