-- Prove2me | solution 1 for PaddedDescent.F.Arith.four_sq_mul_lamG_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:10:37.478369+00:00
-- url     : https://prove2.me/submissions/4a2a8f2d-02e1-4d6a-8689-f732d68a549f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Prog
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Definitions.Def_PaddedDescent_F_ArithTop
import Theorems.Thm_PaddedDescent_F_Arith_lamG_mul_le

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
variable {K g Ub P X : ℕ}
namespace PaddedDescent.F.Arith
theorem _root_.solution (hK : 0 < K) (hP : 4 * (g * P) ≤ K * X) :
    4 * (K ^ 2 * lamG K g Ub P) ≤ 4 * K ^ 2 + 4 * Ub + X := by
  have h := lamG_mul_le K g Ub P
  have key : K * (4 * (K ^ 2 * lamG K g Ub P)) ≤ K * (4 * K ^ 2 + 4 * Ub + X) := by nlinarith
  exact Nat.le_of_mul_le_mul_left key hK
end PaddedDescent.F.Arith
