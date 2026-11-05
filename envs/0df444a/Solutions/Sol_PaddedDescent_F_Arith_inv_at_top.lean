-- Prove2me | solution 1 for PaddedDescent.F.Arith.inv_at_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:27:43.177946+00:00
-- url     : https://prove2.me/submissions/250504bc-90b8-4d99-8c0a-2ba8005298e9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithGlob
import Definitions.Def_PaddedDescent_F_ArithTop
import Definitions.Def_PaddedDescent_F_ArithWalk
import Definitions.Def_PaddedDescent_F_ArithTopInv
import Theorems.Thm_PaddedDescent_F_Arith_one_le_Ktop
import Theorems.Thm_PaddedDescent_F_Arith_Ubof_le
import Theorems.Thm_PaddedDescent_F_Arith_rest_le_Zof
import Theorems.Thm_PaddedDescent_F_Arith_four_mul_Pbof_le
import Theorems.Thm_PaddedDescent_F_Arith_four_sq_mul_lamG_le
import Theorems.Thm_PaddedDescent_F_Arith_inv_top
import Theorems.Thm_PaddedDescent_F_Arith_mul_div_le
import Theorems.Thm_PaddedDescent_decay
import Theorems.Thm_PaddedDescent_gtop_eq
import Theorems.Thm_PaddedDescent_lt_two_pow_mul_div_add_one


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
namespace PaddedDescent.F.Arith
theorem _root_.solution {k Δ s n : ℕ} (hk : k ≤ s) (hΔ : Δ ≤ 2 ^ betaOf s) (hY : Ytop s ^ 6 ≤ n) :
    Inv (depthOf s) (Xof s n) (Zof s) (Qmof k s n) (Wmof k s n) (Lof s n) (depthOf s)
      (lamG (Kseq (depthOf s)) (3 * Kseq (depthOf s) ^ 8) (Ubof k s n) (Pbof Δ s n))
      (Pbof Δ s n * (2 * (3 * Kseq (depthOf s) ^ 8) / Kseq (depthOf s))) 1 := by
  have hK : Kseq (depthOf s) = Ktop s := rfl
  rw [hK, ← gtop_eq]
  have k1 := one_le_Ktop s
  have hP := four_mul_Pbof_le hΔ hY
  have q1 := four_sq_mul_lamG_le (Ub := Ubof k s n) k1 hP
  have q2 := rest_le_Zof s
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hK]
    refine inv_top k1 hP (Ubof_le hk n) (lt_two_pow_mul_div_add_one n s).le ?_ q2
    have h := decay (C := 8) (by norm_num) s
    calc 8963 ^ depthOf s * (2 * (4 * (s + 8) ^ 6) * 2 ^ s) = 8963 ^ depthOf s * (8 * (s + 8) ^ 6 * 2 ^ s) := by ring
      _ ≤ 10000 ^ depthOf s := h
  · rw [hK]
    unfold Qmof
    omega
  · rw [hK]
    have b3 : Pbof Δ s n * (2 * gtop s / Ktop s) ≤ Qmof k s n := by
      have := mul_div_le k1 hP
      unfold Qmof
      omega
    have b4 := Nat.mul_le_mul_right (Ktop s ^ 3) b3
    unfold Wmof
    nlinarith
  · rw [one_mul]
end PaddedDescent.F.Arith
