-- Prove2me | solution 1 for PaddedDescent.F.Arith.pow_le_mul_Kseq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:06:07.293213+00:00
-- url     : https://prove2.me/submissions/6c632228-d36b-46c2-9f0f-f9ea157a411f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Seq
import Definitions.Def_PaddedDescent_F_ArithLevel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_PaddedDescent_F_ArithInv
import Theorems.Thm_PaddedDescent_Kseq_lower


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open Groundwork.Prog (nRect)
namespace PaddedDescent.F.Arith
theorem _root_.solution (j : ℕ) : 10000 ^ j ≤ 8963 ^ j * Kseq j := by
  calc 10000 ^ j ≤ (8963 * 4) ^ j * 256 :=
        le_trans (Nat.pow_le_pow_left (by norm_num) j) (Nat.le_mul_of_pos_right _ (by norm_num))
    _ = 8963 ^ j * (256 * 4 ^ j) := by rw [mul_pow]; ring
    _ ≤ 8963 ^ j * Kseq j := Nat.mul_le_mul_left _ (Kseq_lower j)
end PaddedDescent.F.Arith
