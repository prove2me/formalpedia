-- Prove2me | solution 1 for PaddedDescent.F.Arith.inv_top_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:02:53.684779+00:00
-- url     : https://prove2.me/submissions/79838a01-b5b5-445e-b2a9-6096c3152c55

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Prog
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Definitions.Def_PaddedDescent_F_ArithTop

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
variable {K g Ub P X : ℕ}
namespace PaddedDescent.F.Arith
theorem _root_.solution {A B q Z v X : ℕ} (h3 : A * (2 * v) ≤ B * X) (h4 : A * X ≤ B * X) (h5 : 4 * q ≤ 4 * Z + 4 * v + X) :
    A * q ≤ B * X + A * Z := by
  have h6 := Nat.mul_le_mul_left A h5
  nlinarith
end PaddedDescent.F.Arith
