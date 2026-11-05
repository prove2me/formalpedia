-- Prove2me | solution 1 for PaddedDescent.Kseq_le_gseq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:19:11.738209+00:00
-- url     : https://prove2.me/submissions/2b2cffa3-2577-4db6-a1b5-22cd12f98ccc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Params
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Definitions.Def_PaddedDescent_Seq
import Theorems.Thm_PaddedDescent_two_pow_mul_Kseq_le_gseq

set_option autoImplicit false
section
section
open PaddedDescent
namespace PaddedDescent
theorem _root_.solution (j : ℕ) : Kseq j ≤ gseq j :=
  le_trans (Nat.le_mul_of_pos_left _ (by positivity)) (two_pow_mul_Kseq_le_gseq j)
end PaddedDescent
