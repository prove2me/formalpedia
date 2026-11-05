-- Prove2me | solution 1 for PaddedDescent.Ytop_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:28:02.261358+00:00
-- url     : https://prove2.me/submissions/48c02381-1cf7-4989-bbf8-603076f6f6f9

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
import Theorems.Thm_PaddedDescent_Ytop_le


set_option autoImplicit false
section
section
open PaddedDescent
namespace PaddedDescent
theorem _root_.solution {p : ℕ} (hp : p ≤ 2 ^ 200) (s : ℕ) : Ytop s ^ p ≤ 2 ^ 2 ^ (depthOf s + 211) := by
  have key : 2 ^ (depthOf s + 11) * p ≤ 2 ^ (depthOf s + 211) := by
    calc 2 ^ (depthOf s + 11) * p ≤ 2 ^ (depthOf s + 11) * 2 ^ 200 := Nat.mul_le_mul_left _ hp
      _ = 2 ^ (depthOf s + 211) := by rw [← pow_add]
  calc Ytop s ^ p ≤ (2 ^ 2 ^ (depthOf s + 11)) ^ p := Nat.pow_le_pow_left (Ytop_le s) p
    _ = 2 ^ (2 ^ (depthOf s + 11) * p) := by rw [← pow_mul]
    _ ≤ 2 ^ 2 ^ (depthOf s + 211) := Nat.pow_le_pow_right (by norm_num) key
end PaddedDescent
