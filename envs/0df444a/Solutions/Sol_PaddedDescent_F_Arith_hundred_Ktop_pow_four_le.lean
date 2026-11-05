-- Prove2me | solution 1 for PaddedDescent.F.Arith.hundred_Ktop_pow_four_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:05:00.036516+00:00
-- url     : https://prove2.me/submissions/67b1ded7-0e30-452f-b8e1-fbe8cc45a8d7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithGlob
import Definitions.Def_PaddedDescent_F_ArithTop
import Definitions.Def_PaddedDescent_F_ArithWalk
import Definitions.Def_PaddedDescent_F_ArithTopInv
import Theorems.Thm_PaddedDescent_mul_Ktop_pow_le_Ytop


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
namespace PaddedDescent.F.Arith
theorem _root_.solution (s : ℕ) : 100 * Ktop s ^ 4 ≤ Ytop s :=
  mul_Ktop_pow_le_Ytop (C := 100) (e := 4) (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by norm_num : 7 ≤ 500)))
    (by norm_num) s
end PaddedDescent.F.Arith
