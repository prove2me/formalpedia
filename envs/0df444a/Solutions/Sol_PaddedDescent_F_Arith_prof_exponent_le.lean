-- Prove2me | solution 1 for PaddedDescent.F.Arith.prof_exponent_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:06:25.770203+00:00
-- url     : https://prove2.me/submissions/3255d660-3798-4a06-857e-cbcc4343e53a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithStack
import Definitions.Def_PaddedDescent_F_ArithMark
import Theorems.Thm_PaddedDescent_F_Arith_betaOf_lt_Ytop
import Theorems.Thm_PaddedDescent_overhead_sOf_le_div
import Theorems.Thm_PaddedDescent_size_le_sqrt


set_option autoImplicit false
section
section
set_option exponentiation.threshold 1024
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent
namespace PaddedDescent.F.Arith
theorem _root_.solution {n : ℕ} (hs : 1 ≤ sOf n) :
    (betaOf (sOf n) + Nat.size n) * (Ytop (sOf n) * (layersOf (sOf n) + 2)) ≤ n / 2 ^ sOf n := by
  refine overhead_sOf_le_div (a := 3) (c := 3) hs (by norm_num) (by norm_num) ?_
  obtain ⟨Y, hY⟩ : ∃ Y, Y = Ytop (sOf n) := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = Nat.sqrt n + 1 := ⟨_, rfl⟩
  have h1 := betaOf_lt_Ytop (sOf n)
  have h2 := size_le_sqrt n
  rw [← hY] at h1 ⊢
  rw [← hr]
  have hr1 : 1 ≤ r := by omega
  have hY1 : 1 ≤ Y := by omega
  have hYr : Y ≤ Y * r := Nat.le_mul_of_pos_right _ hr1
  have hrY : r ≤ Y * r := Nat.le_mul_of_pos_left _ hY1
  have e1 : betaOf (sOf n) + Nat.size n ≤ 3 * (Y * r) := by omega
  have e2 : layersOf (sOf n) + 2 ≤ Y := by unfold layersOf; omega
  calc (betaOf (sOf n) + Nat.size n) * (Y * (layersOf (sOf n) + 2)) ≤ 3 * (Y * r) * (Y * Y) := by gcongr
    _ = 3 * Y ^ 3 * r := by ring
end PaddedDescent.F.Arith
