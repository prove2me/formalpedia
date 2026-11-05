-- Prove2me | solution 1 for PaddedDescent.Ytop_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:21:47.796289+00:00
-- url     : https://prove2.me/submissions/9c1a16a4-3924-42aa-8799-b5fd1edb1836

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Params
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Definitions.Def_PaddedDescent_Seq
import Theorems.Thm_PaddedDescent_Ktop_lower
import Theorems.Thm_PaddedDescent_mul_Ktop_pow_le_Ytop

set_option autoImplicit false
section
section
open PaddedDescent
namespace PaddedDescent
theorem _root_.solution (s : ℕ) : 2 ^ (52 * s + 694) ≤ Ytop s := by
  have h := mul_Ktop_pow_le_Ytop (C := 4) (e := 1) (by exact Nat.le_trans (by decide : 4 ≤ (2 : ℕ) ^ 2) (Nat.pow_le_pow_right (by decide) (by decide))) (by norm_num) s
  calc 2 ^ (52 * s + 694) = 4 * 2 ^ (52 * s + 692) := by rw [show 52 * s + 694 = 52 * s + 692 + 2 by ring, pow_add]; ring
    _ ≤ 4 * Ktop s ^ 1 := by rw [pow_one]; exact Nat.mul_le_mul_left _ (Ktop_lower s)
    _ ≤ Ytop s := h
end PaddedDescent
