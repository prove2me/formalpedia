-- Prove2me | solution 1 for PaddedDescent.Ytop_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:55:02.404201+00:00
-- url     : https://prove2.me/submissions/f36d9830-458f-4b52-b570-804affdef9f0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Params
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Definitions.Def_PaddedDescent_Seq
import Theorems.Thm_PaddedDescent_Kseq_upper
import Theorems.Thm_PaddedDescent_Ytop_eq

set_option autoImplicit false
section
section
open PaddedDescent
namespace PaddedDescent
theorem _root_.solution (s : ℕ) : Ytop s ≤ 2 ^ 2 ^ (depthOf s + 11) := by
  have h1 : Ktop s ≤ 2 ^ (104 * 2 ^ depthOf s) := Kseq_upper _
  have h2 : 1 ≤ 2 ^ depthOf s := Nat.one_le_two_pow
  calc Ytop s = 9 * Ktop s ^ 16 := Ytop_eq s
    _ ≤ 2 ^ 4 * (2 ^ (104 * 2 ^ depthOf s)) ^ 16 := Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left h1 16)
    _ = 2 ^ (4 + 104 * 2 ^ depthOf s * 16) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ 2 ^ (depthOf s + 11) := by
      refine Nat.pow_le_pow_right (by norm_num) ?_
      rw [pow_add]
      norm_num
      omega
end PaddedDescent
