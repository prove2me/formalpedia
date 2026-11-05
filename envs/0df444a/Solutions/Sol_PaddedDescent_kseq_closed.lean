-- Prove2me | solution 1 for PaddedDescent.kseq_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:06:41.683877+00:00
-- url     : https://prove2.me/submissions/be46a787-4fa1-4fd1-a07b-218dfdc0c085

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Params
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Definitions.Def_PaddedDescent_Seq
import Theorems.Thm_PaddedDescent_kseq_succ
import Theorems.Thm_PaddedDescent_kseq_zero


set_option autoImplicit false
section
section
open PaddedDescent
namespace PaddedDescent
theorem _root_.solution (j : ℕ) : kseq j + 2 * j + 96 = 104 * 2 ^ j := by
  induction j with
  | zero => rw [kseq_zero]; norm_num
  | succ j ih => rw [kseq_succ, pow_succ]; omega
end PaddedDescent
