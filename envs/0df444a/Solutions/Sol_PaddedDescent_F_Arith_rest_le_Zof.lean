-- Prove2me | solution 1 for PaddedDescent.F.Arith.rest_le_Zof
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:11:38.936132+00:00
-- url     : https://prove2.me/submissions/a9231b88-69d3-4893-83e7-ff087e0d9edd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithGlob
import Definitions.Def_PaddedDescent_F_ArithTop
import Definitions.Def_PaddedDescent_F_ArithWalk
import Definitions.Def_PaddedDescent_F_ArithTopInv
import Theorems.Thm_PaddedDescent_F_Arith_hundred_Ktop_sq_le
import Theorems.Thm_PaddedDescent_F_Arith_cube_le_Ytop

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
namespace PaddedDescent.F.Arith
theorem _root_.solution (s : ℕ) : Ktop s ^ 2 + 8 * (s + 8) ^ 2 * Ytop s ≤ Zof s := by
  have h1 := cube_le_Ytop s
  have h2 := hundred_Ktop_sq_le s
  have h0 : (s + 8) ^ 2 ≤ (s + 8) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h3 : (8 * (s + 8) ^ 2 + 1) * Ytop s ≤ Ytop s * Ytop s := Nat.mul_le_mul_right _ (by omega)
  have e1 : (8 * (s + 8) ^ 2 + 1) * Ytop s = 8 * (s + 8) ^ 2 * Ytop s + Ytop s := by ring
  have e2 : Ytop s * Ytop s = Ytop s ^ 2 := by ring
  unfold Zof
  omega
end PaddedDescent.F.Arith
