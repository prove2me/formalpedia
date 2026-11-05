-- Prove2me | solution 1 for PaddedDescent.F.Arith.small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:10:38.48652+00:00
-- url     : https://prove2.me/submissions/26f377bf-5e5e-4825-8b7a-1a88807f3be3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithGlob
import Definitions.Def_PaddedDescent_F_ArithTop
import Definitions.Def_PaddedDescent_F_ArithWalk
import Definitions.Def_PaddedDescent_F_ArithTopInv
import Theorems.Thm_PaddedDescent_F_Arith_one_le_Ktop
import Theorems.Thm_PaddedDescent_F_Arith_hundred_Ktop_sq_le
import Theorems.Thm_PaddedDescent_F_Arith_Lof_le
import Theorems.Thm_PaddedDescent_overhead_le_div


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
namespace PaddedDescent.F.Arith
theorem _root_.solution {s n : ℕ} (hY : Ytop s ^ 6 ≤ n) :
    5 * Zof s + Lof s n * (2 * Ktop s ^ 2 + 2) + 1 + Ktop s ≤ n / 2 ^ s := by
  refine overhead_le_div (c := 68) (a := 2)
    (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by norm_num : 7 ≤ 500))) hY ?_
  have h1 := Lof_le s n
  have h2 := hundred_Ktop_sq_le s
  have h3 : 1 ≤ Ktop s ^ 2 := Nat.one_le_pow _ _ (one_le_Ktop s)
  have h4 : Ktop s ≤ Ktop s ^ 2 := Nat.le_self_pow (by norm_num) _
  have h5 : 2 * Ktop s ^ 2 + 2 ≤ Ytop s := by omega
  have h6 : Lof s n * (2 * Ktop s ^ 2 + 2) ≤ 2 * Ytop s * (Nat.sqrt n + 1) * Ytop s := Nat.mul_le_mul h1 h5
  have e6 : 2 * Ytop s * (Nat.sqrt n + 1) * Ytop s = 2 * (Ytop s ^ 2 * (Nat.sqrt n + 1)) := by ring
  have h7' : Ytop s ^ 2 ≤ Ytop s ^ 2 * (Nat.sqrt n + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have h7 : Ytop s ≤ Ytop s ^ 2 * (Nat.sqrt n + 1) := le_trans (Nat.le_self_pow (by norm_num) _) h7'
  have e8 : 68 * Ytop s ^ 2 * (Nat.sqrt n + 1) = 68 * (Ytop s ^ 2 * (Nat.sqrt n + 1)) := by ring
  rw [e8]
  unfold Zof
  omega
end PaddedDescent.F.Arith
