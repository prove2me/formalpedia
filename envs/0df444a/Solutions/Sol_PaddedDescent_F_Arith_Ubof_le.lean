-- Prove2me | solution 1 for PaddedDescent.F.Arith.Ubof_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:10:59.918871+00:00
-- url     : https://prove2.me/submissions/1b7edd46-a395-4edc-963c-fa08a6d8f031

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithGlob
import Definitions.Def_PaddedDescent_F_ArithTop
import Definitions.Def_PaddedDescent_F_ArithWalk
import Definitions.Def_PaddedDescent_F_ArithTopInv
import Theorems.Thm_PaddedDescent_F_Arith_cube_le_Ytop
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_PaddedDescent_Ytop_eq_sq


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
namespace PaddedDescent.F.Arith
theorem _root_.solution {k s : ℕ} (hk : k ≤ s) (n : ℕ) : Ubof k s n ≤ 4 * (s + 8) ^ 6 * n + 8 * (s + 8) ^ 2 * Ytop s := by
  have h1 := cube_le_Ytop s
  obtain ⟨Y, hY⟩ : ∃ Y, Y = Ytop s := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x, x = s + 8 := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, β = betaOf s := ⟨_, rfl⟩
  have hβx : β + 3 ≤ x ^ 2 := by rw [hβ, hx, betaOf]; nlinarith
  have hkx : k - 1 ≤ x := by omega
  have hx1 : 1 ≤ x := by omega
  rw [← hY, ← hx] at h1 ⊢
  have e : Ubof k s n = 2 * (2 * β + 6) * ((k - 1) * (n + 2) * (1 + β) + (k - 1) * (n + 1) + Y) := by
    unfold Ubof Ub layersOf
    rw [← hβ, hY, Ytop_eq_sq]
  rw [e]
  have a1 : 2 * β + 6 ≤ 2 * x ^ 2 := by omega
  have a2 : 1 + β ≤ x ^ 2 := by omega
  have a3 : (k - 1) * (n + 2) * (1 + β) + (k - 1) * (n + 1) + Y ≤ x * (n + 2) * (x ^ 2 - 1) + x * (n + 1) + Y := by
    have : 1 + β ≤ x ^ 2 - 1 := by omega
    gcongr
  have hx2 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ hx1
  obtain ⟨q, hq⟩ : ∃ q, x ^ 2 = q + 1 := ⟨x ^ 2 - 1, by omega⟩
  have a4 : x * (n + 2) * (x ^ 2 - 1) + x * (n + 1) + Y ≤ x ^ 3 * n + (2 * x ^ 3 + Y) := by
    have e3 : x ^ 3 = x * (q + 1) := by rw [← hq]; ring
    rw [hq, Nat.add_sub_cancel, e3]
    nlinarith
  have a5 : 2 * x ^ 3 + Y ≤ 2 * Y := by omega
  have hx36 : x ^ 5 ≤ x ^ 6 := Nat.pow_le_pow_right hx1 (by norm_num)
  calc 2 * (2 * β + 6) * ((k - 1) * (n + 2) * (1 + β) + (k - 1) * (n + 1) + Y)
      ≤ 2 * (2 * x ^ 2) * (x ^ 3 * n + 2 * Y) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ a1) (a3.trans (a4.trans (Nat.add_le_add_left a5 _)))
    _ = 4 * x ^ 5 * n + 8 * x ^ 2 * Y := by ring
    _ ≤ 4 * x ^ 6 * n + 8 * x ^ 2 * Y := by gcongr
end PaddedDescent.F.Arith
