-- Prove2me | solution 1 for PaddedDescent.F.Arith.coeff_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:08:03.4147+00:00
-- url     : https://prove2.me/submissions/148ebda4-8a1f-4e7a-aab5-f4b01f659658

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithGlob
import Definitions.Def_PaddedDescent_F_ArithTop
import Definitions.Def_PaddedDescent_F_ArithWalk
import Definitions.Def_PaddedDescent_F_ArithTopInv
import Theorems.Thm_PaddedDescent_F_Arith_lin_le_two_pow

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
namespace PaddedDescent.F.Arith
theorem _root_.solution (s : ℕ) : 4 * (s + 8) ^ 6 ≤ 2 ^ (6 * s + 20) := by
  calc 4 * (s + 8) ^ 6 ≤ 4 * (8 * 2 ^ s) ^ 6 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (lin_le_two_pow s) 6)
    _ = 2 ^ (6 * s + 20) := by rw [mul_pow, ← pow_mul, pow_add, Nat.mul_comm s 6]; norm_num; ring
end PaddedDescent.F.Arith
