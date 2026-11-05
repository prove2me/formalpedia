-- Prove2me | solution 1 for PaddedDescent.F.Arith.Qmof_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:20:45.579772+00:00
-- url     : https://prove2.me/submissions/0a40c088-179b-4133-851a-b54c296ba909

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithGlob
import Definitions.Def_PaddedDescent_F_ArithTop
import Definitions.Def_PaddedDescent_F_ArithWalk
import Definitions.Def_PaddedDescent_F_ArithTopInv
import Theorems.Thm_PaddedDescent_F_Arith_Ytop_sq_le
import Theorems.Thm_PaddedDescent_F_Arith_coeff_le
import Theorems.Thm_PaddedDescent_F_Arith_Ubof_le
import Theorems.Thm_PaddedDescent_F_Arith_rest_le_Zof

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
namespace PaddedDescent.F.Arith
theorem _root_.solution {k s n : ℕ} (hk : k ≤ s) (hY : Ytop s ^ 6 ≤ n) : Qmof k s n + 1 ≤ 2 ^ Lof s n := by
  have h1 := Ubof_le hk n
  have h2 : n < 2 ^ Nat.size n := Nat.lt_size_self n
  have h3 := Ytop_sq_le hY
  have h4 := rest_le_Zof s
  have h5 : Xof s n ≤ n + 1 := Nat.add_le_add_right (Nat.div_le_self _ _) 1
  have a1 := coeff_le s
  have a2 : 4 * (s + 8) ^ 6 * n ≤ 2 ^ (6 * s + 20) * 2 ^ Nat.size n := Nat.mul_le_mul a1 h2.le
  have a3 : 4 * 2 ^ Nat.size n ≤ 2 ^ (6 * s + 20) * 2 ^ Nat.size n :=
    Nat.mul_le_mul_right _ (le_trans (by norm_num : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have e2 : 2 ^ Lof s n = 16 * (2 ^ (6 * s + 20) * 2 ^ Nat.size n) := by
    rw [Lof, show 6 * s + 24 + Nat.size n = 4 + (6 * s + 20 + Nat.size n) by ring, pow_add, pow_add]; norm_num
  rw [e2]
  unfold Qmof
  unfold Zof at h4 ⊢
  omega
end PaddedDescent.F.Arith
