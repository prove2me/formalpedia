-- Prove2me | solution 1 for PaddedDescent.F.Arith.col_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:10:27.562543+00:00
-- url     : https://prove2.me/submissions/16f0e3cc-dfc6-4dfb-a8b4-9d656feb13dc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Seq
import Definitions.Def_PaddedDescent_F_ArithLevel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_PaddedDescent_F_ArithInv
import Theorems.Thm_PaddedDescent_F_Arith_Kseq_mono
import Theorems.Thm_PaddedDescent_F_Arith_pow_le_two_pow_sq
import Theorems.Thm_PaddedDescent_Kseq_le_gseq
import Theorems.Thm_PaddedDescent_Kseq_succ_eq_mul


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open Groundwork.Prog (nRect)
variable {t X Z Qm Wm L j lam B cnt : ℕ}
namespace PaddedDescent.F.Arith
theorem _root_.solution (hj : j + 1 ≤ t) : Kseq j ^ gseq j ≤ 2 ^ Kseq t := by
  calc Kseq j ^ gseq j ≤ 2 ^ (gseq j * gseq j) := pow_le_two_pow_sq (Kseq_le_gseq j)
    _ = 2 ^ Kseq (j + 1) := by rw [Kseq_succ_eq_mul]
    _ ≤ 2 ^ Kseq t := Nat.pow_le_pow_right (by norm_num) (Kseq_mono hj)
end PaddedDescent.F.Arith
