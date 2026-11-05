-- Prove2me | solution 1 for PaddedDescent.F.Arith.pow_succ_le_mul_Kseq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:00:46.227206+00:00
-- url     : https://prove2.me/submissions/45c97fb7-95df-4f70-8740-14ebe2bc5e8c

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
theorem _root_.solution (j : ℕ) : 10000 ^ (j + 1) ≤ 8963 ^ (j + 1) * Kseq j := by
  calc 10000 ^ (j + 1) = 10000 ^ j * 10000 := pow_succ _ _
    _ ≤ (8963 * 4) ^ j * (8963 * 256) := Nat.mul_le_mul (Nat.pow_le_pow_left (by norm_num) j) (by norm_num)
    _ = 8963 ^ (j + 1) * (256 * 4 ^ j) := by rw [mul_pow]; ring
    _ ≤ 8963 ^ (j + 1) * Kseq j := Nat.mul_le_mul_left _ (Kseq_lower j)
end PaddedDescent.F.Arith
