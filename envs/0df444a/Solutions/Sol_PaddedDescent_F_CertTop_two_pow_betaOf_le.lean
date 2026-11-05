-- Prove2me | solution 1 for PaddedDescent.F.CertTop.two_pow_betaOf_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:23:57.027838+00:00
-- url     : https://prove2.me/submissions/4ae8ab82-555c-4fa4-adb5-7f8a90ef893c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_CertSparsify
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_PaddedDescent_F_CertTop
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop
open Groundwork Groundwork.Prog Groundwork.Prog.Count Groundwork.Sparsify
open WidthK (theta)
open WidthK.Prog (stepK)
variable {α : Type} [Enc α]
namespace PaddedDescent.F.CertTop
theorem _root_.solution (n : ℕ) : 2 ^ betaOf (sOf n) ≤ n + 2 ^ 49 := by
  rcases Nat.eq_zero_or_pos (sOf n) with h | h
  · rw [h, show betaOf 0 = 49 from rfl]
    exact Nat.le_add_left _ _
  · have h1 : 2 * sOf n + 6 ≤ Nat.log2 (Nat.log2 n) := by unfold sOf at h ⊢; omega
    have h0 : Nat.log2 n ≠ 0 := by
      intro h0
      rw [h0, Nat.log2_zero] at h1
      omega
    have hn : n ≠ 0 := by
      rintro rfl
      exact h0 Nat.log2_zero
    have h2 := Nat.log2_self_le h0
    have h3 := Nat.log2_self_le hn
    have h4 : sOf n + 7 ≤ 2 ^ (sOf n + 3) := by
      have : sOf n < 2 ^ sOf n := Nat.lt_two_pow_self
      rw [pow_add]
      omega
    have h5 : betaOf (sOf n) ≤ Nat.log2 n :=
      calc (sOf n + 7) ^ 2 ≤ (2 ^ (sOf n + 3)) ^ 2 := Nat.pow_le_pow_left h4 2
        _ = 2 ^ (2 * sOf n + 6) := by rw [← pow_mul]; congr 1; ring
        _ ≤ 2 ^ Nat.log2 (Nat.log2 n) := Nat.pow_le_pow_right (by norm_num) h1
        _ ≤ Nat.log2 n := h2
    exact ((Nat.pow_le_pow_right (by norm_num) h5).trans h3).trans (Nat.le_add_right _ _)
end PaddedDescent.F.CertTop
