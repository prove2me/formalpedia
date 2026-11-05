-- Prove2me | solution 1 for PaddedDescent.F.Arith.size_coeff_le_Ktop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:03:07.038002+00:00
-- url     : https://prove2.me/submissions/a5a83c8b-c197-4670-9e5f-acb702451d98

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithGlob
import Definitions.Def_PaddedDescent_F_ArithTop
import Definitions.Def_PaddedDescent_F_ArithWalk
import Definitions.Def_PaddedDescent_F_ArithTopInv
import Theorems.Thm_PaddedDescent_two_pow_betaOf_le_Ktop


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
namespace PaddedDescent.F.Arith
theorem _root_.solution {Δ s : ℕ} (hΔ : Δ ≤ 2 ^ betaOf s) : 16 * (2 + betaOf s) * (Δ + 4) * 2 ^ s ≤ Ktop s := by
  obtain ⟨β, hβ⟩ : ∃ β, β = betaOf s := ⟨_, rfl⟩
  have h0 := two_pow_betaOf_le_Ktop s
  rw [← hβ] at hΔ h0 ⊢
  have h1 : β + 1 ≤ 2 ^ β := Nat.lt_two_pow_self
  have h3 : 2 + β ≤ 2 * 2 ^ β := by omega
  have h4 : Δ + 4 ≤ 8 * 2 ^ β := by omega
  calc 16 * (2 + β) * (Δ + 4) * 2 ^ s ≤ 16 * (2 * 2 ^ β) * (8 * 2 ^ β) * 2 ^ s :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ h3) h4)
    _ = 2 ^ (8 + β + β + s) := by rw [pow_add, pow_add, pow_add]; norm_num; ring
    _ ≤ 2 ^ (4 * β + 10 * s + 1000) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ Ktop s := h0
end PaddedDescent.F.Arith
