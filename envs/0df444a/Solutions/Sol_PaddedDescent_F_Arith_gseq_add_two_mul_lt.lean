-- Prove2me | solution 1 for PaddedDescent.F.Arith.gseq_add_two_mul_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:57:04.983946+00:00
-- url     : https://prove2.me/submissions/d47a4a66-4975-4a6d-ad87-f0303119b007

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Seq
import Definitions.Def_PaddedDescent_F_Prog
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_PaddedDescent_F_ArithCol
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_PaddedDescent_Kseq_ge
import Theorems.Thm_PaddedDescent_Kseq_le_gseq
import Theorems.Thm_PaddedDescent_gseq_eq
import Theorems.Thm_PaddedDescent_kseq_closed


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent
namespace PaddedDescent.F.Arith
theorem _root_.solution (j : ℕ) : (gseq j + 2) * Kseq j < 2 ^ 2 ^ (9 + j) := by
  have h1 := kseq_closed j
  have h2 : 2 ≤ gseq j := le_trans (by norm_num) ((Kseq_ge j).trans (Kseq_le_gseq j))
  have h3 : (2 : ℕ) ^ (9 + j) = 512 * 2 ^ j := by rw [pow_add]; norm_num
  calc (gseq j + 2) * Kseq j ≤ (2 * gseq j) * Kseq j := Nat.mul_le_mul_right _ (by omega)
    _ = 2 ^ (1 + (kseq j + 47 + j) + kseq j) := by rw [gseq_eq, Kseq]; ring
    _ < 2 ^ 2 ^ (9 + j) := Nat.pow_lt_pow_right (by norm_num) (by omega)
end PaddedDescent.F.Arith
