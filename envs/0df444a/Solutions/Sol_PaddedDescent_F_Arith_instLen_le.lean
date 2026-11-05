-- Prove2me | solution 1 for PaddedDescent.F.Arith.instLen_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:59:52.353993+00:00
-- url     : https://prove2.me/submissions/3a0fa0d0-40a0-4f29-9197-0ff2e86a846c

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
theorem _root_.solution (K lam B : ℕ) : instLen K lam B ≤ 2 ^ ((K - 1) * lam) * (K * (3 * B + 14) + 4 * lam + 10) := by
  have h1 : 1 ≤ 2 ^ ((K - 1) * lam) := Nat.one_le_two_pow
  obtain ⟨p, hp⟩ : ∃ p, 2 ^ ((K - 1) * lam) = p + 1 := ⟨2 ^ ((K - 1) * lam) - 1, by omega⟩
  unfold instLen
  rw [hp]
  nlinarith [Nat.zero_le (p * lam), Nat.zero_le (p * K), Nat.zero_le p]
end PaddedDescent.F.Arith
