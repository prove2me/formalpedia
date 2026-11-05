-- Prove2me | solution 1 for PaddedDescent.F.Arith.pow_facts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:00:25.772835+00:00
-- url     : https://prove2.me/submissions/fd50f64e-9eb9-4785-99e5-8ccf4599e2f6

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
theorem _root_.solution {K g : ℕ} (hg : 2 * K ≤ g) :
    24 * K ^ 3 ≤ 16 * (g * g) ^ 3 ∧ 2 * K ^ 2 ≤ (g * g) ^ 2 := by
  have hgg : 2 * K ≤ g * g := le_trans hg (Nat.le_mul_self g)
  have h3 : (2 * K) ^ 3 ≤ (g * g) ^ 3 := Nat.pow_le_pow_left hgg 3
  have h2 : (2 * K) ^ 2 ≤ (g * g) ^ 2 := Nat.pow_le_pow_left hgg 2
  have e3 : (2 * K) ^ 3 = 8 * K ^ 3 := by ring
  have e2 : (2 * K) ^ 2 = 4 * K ^ 2 := by ring
  constructor <;> omega
end PaddedDescent.F.Arith
