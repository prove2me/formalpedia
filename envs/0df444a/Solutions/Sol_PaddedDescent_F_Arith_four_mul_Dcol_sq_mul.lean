-- Prove2me | solution 1 for PaddedDescent.F.Arith.four_mul_Dcol_sq_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:56:58.926308+00:00
-- url     : https://prove2.me/submissions/e1de1486-bcd8-49c0-87d7-cd639df6888f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Seq
import Definitions.Def_PaddedDescent_F_Prog
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_PaddedDescent_F_ArithCol

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent
namespace PaddedDescent.F.Arith
theorem _root_.solution (j : ℕ) : 4 * Dcol ^ 2 * 2 ^ (9 + j) * Kseq j = gseq j := by
  rw [gseq, Lseq, Dcol, show 47 + j = 38 + (9 + j) by omega, pow_add 2 38]
  ring
end PaddedDescent.F.Arith
