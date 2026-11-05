-- Prove2me | solution 1 for PaddedDescent.Kseq_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:17:24.689604+00:00
-- url     : https://prove2.me/submissions/ce13ea18-e06d-4dae-b152-d1ff9825bd9f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Params
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Definitions.Def_PaddedDescent_Seq
import Theorems.Thm_PaddedDescent_kseq_ge__b51875

set_option autoImplicit false
section
section
open PaddedDescent
namespace PaddedDescent
theorem _root_.solution (j : ℕ) : 256 * 4 ^ j ≤ Kseq j := by
  have h := kseq_ge j
  calc 256 * 4 ^ j = 2 ^ (8 + 2 * j) := by rw [pow_add, pow_mul]; norm_num
    _ ≤ 2 ^ kseq j := Nat.pow_le_pow_right (by norm_num) (by omega)
end PaddedDescent
