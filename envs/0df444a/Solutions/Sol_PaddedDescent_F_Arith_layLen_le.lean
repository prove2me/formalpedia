-- Prove2me | solution 1 for PaddedDescent.F.Arith.layLen_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:08:39.078874+00:00
-- url     : https://prove2.me/submissions/f14b0e5e-9608-4ae9-887a-50a607860a1e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithStack
import Definitions.Def_PaddedDescent_F_ArithMark
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_PaddedDescent_F_Arith_clause_word_le
import Theorems.Thm_PaddedDescent_F_Arith_le_pad_of_le
import Theorems.Thm_PaddedDescent_F_Arith_two_pow_betaOf_le


set_option autoImplicit false
section
section
set_option exponentiation.threshold 1024
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent
namespace PaddedDescent.F.Arith
theorem _root_.solution {k Δ n C₀ F : ℕ} (hs : 1 ≤ sOf n) (hC : 1 ≤ C₀) (hF : 2 ^ (C₀ * (n / 2 ^ sOf n + 1)) ≤ F) (hk : k ≤ sOf n)
    (hΔ : Δ ≤ 2 ^ betaOf (sOf n)) : layLen k n (Δ * n) (layersOf (sOf n)) ≤ F := by
  refine le_pad_of_le hs hC hF ?_
  obtain ⟨a, ha⟩ : ∃ a, a = 2 ^ Nat.size n := ⟨_, rfl⟩
  have hn : n < a := ha ▸ Nat.lt_size_self n
  have hbig := two_pow_betaOf_le hs
  have hlt : 4 * betaOf (sOf n) + 10 * sOf n + 1000 < 2 ^ (4 * betaOf (sOf n) + 10 * sOf n + 1000) := Nat.lt_two_pow_self
  have h1 : Δ ≤ a := (hΔ.trans (Nat.pow_le_pow_right (by norm_num) (by omega))).trans (hbig.trans hn.le)
  have h2 : layersOf (sOf n) + 1 ≤ a := by
    unfold layersOf
    omega
  have h3 := clause_word_le hn (show k < a by omega) (show 4 ≤ a by omega)
  have ha1 : 1 ≤ a := by omega
  have h5 : a ≤ a ^ 5 := Nat.le_self_pow (by norm_num) _
  have h9 : a ^ 5 ≤ a ^ 9 := Nat.pow_le_pow_right ha1 (by norm_num)
  unfold layLen
  calc Δ * n * (k * (3 * n + 5) + 10) + 4 * (layersOf (sOf n) + 1) + 2 ≤ a * a * a ^ 3 + 4 * a + 2 := by
        gcongr
    _ = a ^ 5 + 4 * a + 2 := by ring
    _ ≤ 2 ^ 30 * a ^ 9 := by
      norm_num
      omega
    _ = 2 ^ (9 * Nat.size n + 30) := by rw [ha, ← pow_mul, ← pow_add]; congr 1; ring
end PaddedDescent.F.Arith
