-- Prove2me | solution 1 for PaddedDescent.F.Arith.four_mul_Pbof_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:21:07.896376+00:00
-- url     : https://prove2.me/submissions/d65227f6-e495-48a7-a3ee-5f75e93c2c7b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithGlob
import Definitions.Def_PaddedDescent_F_ArithTop
import Definitions.Def_PaddedDescent_F_ArithWalk
import Definitions.Def_PaddedDescent_F_ArithTopInv
import Theorems.Thm_PaddedDescent_F_Arith_gtop_pos
import Theorems.Thm_PaddedDescent_F_Arith_gtop_le_Ytop
import Theorems.Thm_PaddedDescent_F_Arith_size_coeff_le_Ktop
import Theorems.Thm_PaddedDescent_F_Arith_Ytop_le_Xof
import Theorems.Thm_PaddedDescent_F_Arith_mul_div_le
import Theorems.Thm_PaddedDescent_lt_two_pow_mul_div_add_one


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
namespace PaddedDescent.F.Arith
theorem _root_.solution {Δ s n : ℕ} (hΔ : Δ ≤ 2 ^ betaOf s) (hY : Ytop s ^ 6 ≤ n) : 4 * (gtop s * Pbof Δ s n) ≤ Ktop s * Xof s n := by
  have hg := gtop_pos s
  have h1 : gtop s * Mark.qv (gtop s) n ≤ n + gtop s := by
    have := Nat.mul_div_le (n + gtop s - 1) (gtop s)
    unfold Mark.qv
    omega
  have h2 := size_coeff_le_Ktop hΔ
  have h3 : n ≤ 2 ^ s * Xof s n := (lt_two_pow_mul_div_add_one n s).le
  have h4 := Ytop_le_Xof hY
  have h5 := gtop_le_Ytop s
  obtain ⟨c, hc⟩ : ∃ c, c = 8 * (2 + betaOf s) * (Δ + 4) := ⟨_, rfl⟩
  have h2' : 2 * c * 2 ^ s ≤ Ktop s := by rw [hc]; calc _ = 16 * (2 + betaOf s) * (Δ + 4) * 2 ^ s := by ring
    _ ≤ Ktop s := h2
  have h6 : 2 * c ≤ Ktop s := le_trans (Nat.le_mul_of_pos_right _ (by positivity)) h2'
  have e : 4 * (gtop s * Pbof Δ s n) = c * (gtop s * Mark.qv (gtop s) n) := by
    rw [hc]; unfold Pbof Pb; ring
  have hX : Xof s n = n / 2 ^ s + 1 := rfl
  rw [e]
  have b1 : c * (gtop s * Mark.qv (gtop s) n) ≤ c * (2 ^ s * Xof s n) + c * gtop s := by
    calc c * (gtop s * Mark.qv (gtop s) n) ≤ c * (n + gtop s) := Nat.mul_le_mul_left _ h1
      _ ≤ c * (2 ^ s * Xof s n + gtop s) := Nat.mul_le_mul_left _ (by omega)
      _ = c * (2 ^ s * Xof s n) + c * gtop s := by ring
  have b2 : 2 * (c * (2 ^ s * Xof s n)) ≤ Ktop s * Xof s n := by
    calc 2 * (c * (2 ^ s * Xof s n)) = 2 * c * 2 ^ s * Xof s n := by ring
      _ ≤ Ktop s * Xof s n := Nat.mul_le_mul_right _ h2'
  have b3 : 2 * (c * gtop s) ≤ Ktop s * Xof s n := by
    calc 2 * (c * gtop s) = 2 * c * gtop s := by ring
      _ ≤ Ktop s * Xof s n := Nat.mul_le_mul h6 (by omega)
  omega
end PaddedDescent.F.Arith
