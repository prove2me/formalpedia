-- Prove2me | solution 1 for PaddedDescent.F.Arith.colOK_seq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:03:16.11201+00:00
-- url     : https://prove2.me/submissions/355a7e96-3b27-4614-baf2-7d974b28c0d7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Seq
import Definitions.Def_PaddedDescent_F_Prog
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_PaddedDescent_F_ArithCol
import Theorems.Thm_PaddedDescent_F_Arith_four_mul_Dcol_sq_mul
import Theorems.Thm_PaddedDescent_F_Arith_gseq_add_two_mul_lt

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent
namespace PaddedDescent.F.Arith
theorem _root_.solution (j : ℕ) : ColOK (Kseq j) (gseq j) :=
  ⟨2 ^ (9 + j), (four_mul_Dcol_sq_mul j).le, gseq_add_two_mul_lt j⟩
end PaddedDescent.F.Arith
