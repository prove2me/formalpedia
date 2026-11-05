-- Prove2me | solution 1 for PaddedDescent.F.Arith.clauses_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:06:24.684103+00:00
-- url     : https://prove2.me/submissions/1d77a355-ba51-461b-9aaa-7545a740173f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithStack
import Definitions.Def_PaddedDescent_F_ArithMark

set_option autoImplicit false
section
section
set_option exponentiation.threshold 1024
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent
namespace PaddedDescent.F.Arith
theorem _root_.solution {Δ s : ℕ} (hΔ : Δ ≤ 2 ^ betaOf s) (n : ℕ) : Δ * n + 1 ≤ 2 ^ (betaOf s + Nat.size n) := by
  have h2 : n + 1 ≤ 2 ^ Nat.size n := Nat.lt_size_self n
  have h3 : 1 ≤ 2 ^ betaOf s := Nat.one_le_two_pow
  calc Δ * n + 1 ≤ 2 ^ betaOf s * n + 2 ^ betaOf s := Nat.add_le_add (Nat.mul_le_mul_right _ hΔ) h3
    _ = 2 ^ betaOf s * (n + 1) := by ring
    _ ≤ 2 ^ betaOf s * 2 ^ Nat.size n := Nat.mul_le_mul_left _ h2
    _ = 2 ^ (betaOf s + Nat.size n) := (pow_add _ _ _).symm
end PaddedDescent.F.Arith
