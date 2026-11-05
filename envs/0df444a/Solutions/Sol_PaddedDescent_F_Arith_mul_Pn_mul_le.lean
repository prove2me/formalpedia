-- Prove2me | solution 1 for PaddedDescent.F.Arith.mul_Pn_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:59:35.869697+00:00
-- url     : https://prove2.me/submissions/5222427f-5186-4359-bba9-d85ae2d4d343

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Prog
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Definitions.Def_PaddedDescent_F_ArithLevel

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
namespace PaddedDescent.F.Arith
theorem _root_.solution (K g lam : ℕ) : K * (Pn g lam * (2 * g / K)) ≤ 4 * (g ^ 4 * lam) := by
  have m1 : 2 * g / K * K ≤ 2 * g := Nat.div_mul_le_self _ _
  calc K * (Pn g lam * (2 * g / K)) = Pn g lam * (2 * g / K * K) := by ring
    _ ≤ Pn g lam * (2 * g) := Nat.mul_le_mul_left _ m1
    _ = 4 * (g ^ 4 * lam) := by unfold Pn; ring
end PaddedDescent.F.Arith
