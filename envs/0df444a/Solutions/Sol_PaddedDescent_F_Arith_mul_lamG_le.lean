-- Prove2me | solution 1 for PaddedDescent.F.Arith.mul_lamG_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:16:23.404181+00:00
-- url     : https://prove2.me/submissions/342a3450-406c-4093-99ea-91b882272363

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Prog
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Definitions.Def_PaddedDescent_F_ArithTop
import Theorems.Thm_PaddedDescent_F_Arith_four_sq_mul_lamG_le

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
variable {K g Ub P X : ℕ}
namespace PaddedDescent.F.Arith
theorem _root_.solution {r : ℕ} (hK : 0 < K) (hP : 4 * (g * P) ≤ K * X) (hU : Ub ≤ K * X + r) :
    (K - 1) * lamG K g Ub P ≤ K + 2 * X + r := by
  have h1 := four_sq_mul_lamG_le (Ub := Ub) hK hP
  have h2 : X ≤ K * X := Nat.le_mul_of_pos_left _ hK
  have h3 : r ≤ K * r := Nat.le_mul_of_pos_left _ hK
  have key : K * (K * lamG K g Ub P) ≤ K * (K + 2 * X + r) := by nlinarith
  exact le_trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) (Nat.le_of_mul_le_mul_left key hK)
end PaddedDescent.F.Arith
