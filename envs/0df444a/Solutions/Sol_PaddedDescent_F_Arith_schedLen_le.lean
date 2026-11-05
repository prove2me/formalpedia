-- Prove2me | solution 1 for PaddedDescent.F.Arith.schedLen_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:08:36.459394+00:00
-- url     : https://prove2.me/submissions/b3e12d05-251b-44a8-88c4-04da03972bed

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithStack
import Definitions.Def_PaddedDescent_F_ArithCol
import Definitions.Def_PaddedDescent_F_ArithSched
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_PaddedDescent_F_Arith_le_pad_of_le
import Theorems.Thm_PaddedDescent_Ktop_le_Ytop
import Theorems.Thm_PaddedDescent_Ytop_sOf_pow_le
import Theorems.Thm_PaddedDescent_lin_lt_Ytop
import Theorems.Thm_PaddedDescent_two_pow_le_Ktop


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F
open Groundwork PaddedDescent.F.Lists
open Arith
open PaddedDescent.F.Arith
namespace PaddedDescent.F.Arith
theorem _root_.solution {n C₀ F : ℕ} (hs : 1 ≤ sOf n) (hC : 1 ≤ C₀) (hF : 2 ^ (C₀ * (n / 2 ^ sOf n + 1)) ≤ F) :
    schedLen (depthOf (sOf n)) ≤ F := by
  refine le_pad_of_le hs hC hF ?_
  obtain ⟨Y, hY⟩ : ∃ Y, Y = Ytop (sOf n) := ⟨_, rfl⟩
  have h1 : depthOf (sOf n) + 1 ≤ Y := by
    have := lin_lt_Ytop (sOf n)
    unfold depthOf
    omega
  have h2 : Kseq (depthOf (sOf n)) ≤ Y := hY ▸ Ktop_le_Ytop (sOf n)
  have h2' : Lseq (depthOf (sOf n)) ≤ Y := by
    obtain ⟨u, hu, hu'⟩ : ∃ u, depthOf (sOf n) = u + 1 ∧ 46 ≤ u := ⟨19 * sOf n / 3 + 699, rfl, by omega⟩
    have e0 : 47 + depthOf (sOf n) ≤ 2 ^ depthOf (sOf n) := by
      have : u + 1 ≤ 2 ^ u := Nat.lt_two_pow_self
      rw [hu, pow_succ]
      omega
    exact hY ▸ (two_pow_le_Ktop e0).trans (Ktop_le_Ytop (sOf n))
  have h3 : Y ^ 2 ≤ n := hY ▸ Ytop_sOf_pow_le (p := 2) (by norm_num) hs
  have h4 : 1 ≤ Y := by omega
  have h5 : n < 2 ^ Nat.size n := Nat.lt_size_self n
  have h6 : schedLen (depthOf (sOf n)) ≤ 28 * n := by
    unfold schedLen
    calc (depthOf (sOf n) + 1) * (8 * Kseq (depthOf (sOf n)) + 8) + 4 * Lseq (depthOf (sOf n)) + 8 ≤ Y * (8 * Y + 8) + 4 * Y + 8 := by gcongr
      _ ≤ 28 * Y ^ 2 := by nlinarith
      _ ≤ 28 * n := by omega
  have h7 : 2 ^ (9 * Nat.size n + 30) = 2 ^ 30 * (2 ^ Nat.size n) ^ 9 := by rw [← pow_mul, ← pow_add]; congr 1; ring
  have h8 : 2 ^ Nat.size n ≤ (2 ^ Nat.size n) ^ 9 := Nat.le_self_pow (by norm_num) _
  rw [h7]
  norm_num
  omega
end PaddedDescent.F.Arith
