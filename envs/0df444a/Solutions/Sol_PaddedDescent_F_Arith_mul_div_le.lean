-- Prove2me | solution 1 for PaddedDescent.F.Arith.mul_div_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:50:06.19747+00:00
-- url     : https://prove2.me/submissions/633d5faf-b6b9-4eed-92b6-d1ad73696b8e

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
theorem _root_.solution (hK : 0 < K) (hP : 4 * (g * P) ≤ K * X) : P * (2 * g / K) ≤ X := by
  have m1 : 2 * g / K * K ≤ 2 * g := Nat.div_mul_le_self _ _
  have h1 : K * (P * (2 * g / K)) ≤ 2 * (g * P) := by
    calc K * (P * (2 * g / K)) = P * (2 * g / K * K) := by ring
      _ ≤ P * (2 * g) := Nat.mul_le_mul_left _ m1
      _ = 2 * (g * P) := by ring
  exact Nat.le_of_mul_le_mul_left (by omega : K * (P * (2 * g / K)) ≤ K * X) hK
end PaddedDescent.F.Arith
