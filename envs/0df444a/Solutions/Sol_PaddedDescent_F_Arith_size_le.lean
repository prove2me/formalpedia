-- Prove2me | solution 1 for PaddedDescent.F.Arith.size_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:50:12.975801+00:00
-- url     : https://prove2.me/submissions/6496d2d7-f807-4923-a891-ba3ebadc4ff8

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
theorem _root_.solution (hg : 0 < g) (hKg : K ≤ g) (hP : 4 * (g * P) ≤ K * X) : P ≤ X := by
  have h1 : K * X ≤ g * X := Nat.mul_le_mul_right _ hKg
  exact Nat.le_of_mul_le_mul_left (by omega : g * P ≤ g * X) hg
end PaddedDescent.F.Arith
