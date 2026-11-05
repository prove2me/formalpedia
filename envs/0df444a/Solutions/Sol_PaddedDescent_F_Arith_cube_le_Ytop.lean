-- Prove2me | solution 1 for PaddedDescent.F.Arith.cube_le_Ytop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:08:07.313849+00:00
-- url     : https://prove2.me/submissions/c9debb6e-a968-4cb3-a610-986a04678741

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithGlob
import Definitions.Def_PaddedDescent_F_ArithTop
import Definitions.Def_PaddedDescent_F_ArithWalk
import Definitions.Def_PaddedDescent_F_ArithTopInv
import Theorems.Thm_PaddedDescent_F_Arith_lin_le_two_pow
import Theorems.Thm_PaddedDescent_Ytop_lower


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
namespace PaddedDescent.F.Arith
theorem _root_.solution (s : ℕ) : 8 * (s + 8) ^ 3 + 1 ≤ Ytop s := by
  have h1 : 1 ≤ 2 ^ (3 * s) := Nat.one_le_two_pow
  calc 8 * (s + 8) ^ 3 + 1 ≤ 8 * (8 * 2 ^ s) ^ 3 + 1 := by gcongr; exact lin_le_two_pow s
    _ = 2 ^ 12 * 2 ^ (3 * s) + 1 := by rw [mul_pow, ← pow_mul, Nat.mul_comm s 3]; norm_num; ring
    _ ≤ 2 ^ 13 * 2 ^ (3 * s) := by omega
    _ = 2 ^ (13 + 3 * s) := by rw [← pow_add]
    _ ≤ 2 ^ (52 * s + 694) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ Ytop s := Ytop_lower s
end PaddedDescent.F.Arith
