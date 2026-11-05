-- Prove2me | solution 1 for PaddedDescent.F.Arith.top_tab
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:28:22.219699+00:00
-- url     : https://prove2.me/submissions/a4ea33bb-8c85-459f-9b36-4a0ef23cf576

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithGlob
import Definitions.Def_PaddedDescent_F_ArithTop
import Definitions.Def_PaddedDescent_F_ArithWalk
import Definitions.Def_PaddedDescent_F_ArithTopInv
import Theorems.Thm_PaddedDescent_F_Arith_one_le_Ktop
import Theorems.Thm_PaddedDescent_F_Arith_Ubof_le
import Theorems.Thm_PaddedDescent_F_Arith_coeff_le_Ktop
import Theorems.Thm_PaddedDescent_F_Arith_rest_le_Zof
import Theorems.Thm_PaddedDescent_F_Arith_small
import Theorems.Thm_PaddedDescent_F_Arith_four_mul_Pbof_le
import Theorems.Thm_PaddedDescent_F_Arith_two_pow_le_of_le
import Theorems.Thm_PaddedDescent_F_Arith_mul_lamG_le
import Theorems.Thm_PaddedDescent_lt_two_pow_mul_div_add_one


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
variable {k Δ s n F : ℕ}
namespace PaddedDescent.F.Arith
theorem _root_.solution (hk : k ≤ s) (hΔ : Δ ≤ 2 ^ betaOf s) (hY : Ytop s ^ 6 ≤ n) (hF : 2 ^ (8 * Xof s n) ≤ F) :
    2 ^ ((Kseq (depthOf s) - 1) * lamG (Kseq (depthOf s)) (3 * Kseq (depthOf s) ^ 8) (Ubof k s n) (Pbof Δ s n)) ≤ F := by
  have hU : Ubof k s n ≤ Ktop s * Xof s n + 8 * (s + 8) ^ 2 * Ytop s := by
    refine le_trans (Ubof_le hk n) (Nat.add_le_add_right ?_ _)
    calc 4 * (s + 8) ^ 6 * n ≤ 4 * (s + 8) ^ 6 * (2 ^ s * Xof s n) :=
          Nat.mul_le_mul_left _ (lt_two_pow_mul_div_add_one n s).le
      _ = 4 * (s + 8) ^ 6 * 2 ^ s * Xof s n := by ring
      _ ≤ Ktop s * Xof s n := Nat.mul_le_mul_right _ (coeff_le_Ktop s)
  have h1 : (Ktop s - 1) * lamG (Ktop s) (gtop s) (Ubof k s n) (Pbof Δ s n) ≤ Ktop s + 2 * Xof s n + 8 * (s + 8) ^ 2 * Ytop s :=
    mul_lamG_le (one_le_Ktop s) (four_mul_Pbof_le hΔ hY) hU
  have h2 := small hY
  have h3 := rest_le_Zof s
  have hX : Xof s n = n / 2 ^ s + 1 := rfl
  exact two_pow_le_of_le hF (le_trans h1 (by omega))
end PaddedDescent.F.Arith
