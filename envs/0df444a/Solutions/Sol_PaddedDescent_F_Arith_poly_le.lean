-- Prove2me | solution 1 for PaddedDescent.F.Arith.poly_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:27:23.483202+00:00
-- url     : https://prove2.me/submissions/951d3ca1-c55c-49d6-b0ec-e8dcb83354e0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithGlob
import Definitions.Def_PaddedDescent_F_ArithTop
import Definitions.Def_PaddedDescent_F_ArithWalk
import Definitions.Def_PaddedDescent_F_ArithTopInv
import Theorems.Thm_PaddedDescent_F_Arith_one_le_Ktop
import Theorems.Thm_PaddedDescent_F_Arith_hundred_Ktop_pow_four_le
import Theorems.Thm_PaddedDescent_F_Arith_hundred_Ytop_le
import Theorems.Thm_PaddedDescent_F_Arith_Qmof_lt
import Theorems.Thm_PaddedDescent_F_Arith_lt_two_pow_Lof
import Theorems.Thm_Groundwork_PolyT_congr


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
namespace PaddedDescent.F.Arith
theorem _root_.solution {k s n : ℕ} (hk : k ≤ s) (hY : Ytop s ^ 6 ≤ n) :
    Kseq (depthOf s) * (3 * Wmof k s n + 14) + 4 * Qmof k s n + 10 ≤ 2 ^ (2 * Lof s n) := by
  have hK : Kseq (depthOf s) = Ktop s := rfl
  rw [hK]
  have h1 := Qmof_lt hk hY
  have h2 := hundred_Ktop_pow_four_le s
  have h3 := hundred_Ytop_le hY
  have h4 := lt_two_pow_Lof s n
  have h5 : Ktop s ≤ Ktop s ^ 4 := Nat.le_self_pow (by norm_num) _
  have h6 : 1 ≤ Ktop s ^ 4 := Nat.one_le_pow _ _ (one_le_Ktop s)
  have a1 : 51 * Ktop s ^ 4 + 14 * Ktop s + 14 ≤ 2 ^ Lof s n := by omega
  have a2 : Ktop s * (3 * Wmof k s n + 14) + 4 * Qmof k s n + 10
      ≤ (51 * Ktop s ^ 4 + 14 * Ktop s + 14) * (Qmof k s n + 1) := by
    unfold Wmof
    nlinarith [Nat.zero_le (Ktop s ^ 4), Nat.zero_le (Ktop s * Qmof k s n)]
  calc Ktop s * (3 * Wmof k s n + 14) + 4 * Qmof k s n + 10
      ≤ (51 * Ktop s ^ 4 + 14 * Ktop s + 14) * (Qmof k s n + 1) := a2
    _ ≤ 2 ^ Lof s n * 2 ^ Lof s n := Nat.mul_le_mul a1 h1
    _ = 2 ^ (2 * Lof s n) := by rw [← pow_add]; congr 1; ring
end PaddedDescent.F.Arith
