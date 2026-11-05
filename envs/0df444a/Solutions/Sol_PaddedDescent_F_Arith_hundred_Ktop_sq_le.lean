-- Prove2me | solution 1 for PaddedDescent.F.Arith.hundred_Ktop_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:07:07.165627+00:00
-- url     : https://prove2.me/submissions/936ee8bb-1753-4560-abe4-09590968787e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithGlob
import Definitions.Def_PaddedDescent_F_ArithTop
import Definitions.Def_PaddedDescent_F_ArithWalk
import Definitions.Def_PaddedDescent_F_ArithTopInv
import Theorems.Thm_PaddedDescent_F_Arith_one_le_Ktop
import Theorems.Thm_PaddedDescent_F_Arith_hundred_Ktop_pow_four_le

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
namespace PaddedDescent.F.Arith
theorem _root_.solution (s : ℕ) : 100 * Ktop s ^ 2 ≤ Ytop s :=
  le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (one_le_Ktop s) (by norm_num))) (hundred_Ktop_pow_four_le s)
end PaddedDescent.F.Arith
