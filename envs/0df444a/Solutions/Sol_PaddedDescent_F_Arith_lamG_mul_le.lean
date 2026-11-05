-- Prove2me | solution 1 for PaddedDescent.F.Arith.lamG_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:01:40.906194+00:00
-- url     : https://prove2.me/submissions/c1618b28-8a29-44c7-b4c8-2ba253899479

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
theorem _root_.solution (K g Ub P : ℕ) : lamG K g Ub P * K ^ 3 ≤ K ^ 3 + K * Ub + g * P :=
  Nat.div_mul_le_self _ _
end PaddedDescent.F.Arith
