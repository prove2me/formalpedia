-- Prove2me | solution 1 for PaddedDescent.F.Arith.six_cube_mul_cube_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:00:24.552895+00:00
-- url     : https://prove2.me/submissions/08875861-3bcf-4a8b-8a86-8df59b30ea56

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
theorem _root_.solution {K g : ℕ} (hg : 2 * K ≤ g) : 6 * g ^ 3 * K ^ 3 ≤ (g * g) ^ 3 := by
  have h : (2 * K) ^ 3 ≤ g ^ 3 := Nat.pow_le_pow_left hg 3
  calc 6 * g ^ 3 * K ^ 3 ≤ g ^ 3 * (2 * K) ^ 3 := by
        have : (2 * K) ^ 3 = 8 * K ^ 3 := by ring
        rw [this]; nlinarith [Nat.zero_le (g ^ 3 * K ^ 3)]
    _ ≤ g ^ 3 * g ^ 3 := Nat.mul_le_mul_left _ h
    _ = (g * g) ^ 3 := by ring
end PaddedDescent.F.Arith
