-- Prove2me | solution 1 for PaddedDescent.F.Arith.pow_le_two_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:59:51.074911+00:00
-- url     : https://prove2.me/submissions/2511c835-1eb6-42dd-8b6a-fc7fab4925c6

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
theorem _root_.solution (K g : ℕ) : K ^ g ≤ 2 ^ (K * g) := by
  rw [pow_mul]
  exact Nat.pow_le_pow_left (Nat.lt_two_pow_self).le g
end PaddedDescent.F.Arith
