-- Prove2me | solution 1 for PiecesCounted.Data.Is.cap_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:49:08.385532+00:00
-- url     : https://prove2.me/submissions/ea651760-f69b-4777-a326-cd5946bee7a0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCounted_Basic
import Definitions.Def_GeneralPieces_DefGenPieces_Conv
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Sizes
import Theorems.Thm_GeneralPieces_DefGenPieces_logb_le


set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog
namespace PiecesCounted
namespace Data.Is
theorem _root_.solution {D : Data} {ρ : ℝ} {c : ℕ} (h : D.Is ρ c) {lam : ℕ} (hl : 1 ≤ lam) {i : ℤ} (hi : i ∈ (D.fam lam).I) (tr : Bool) : D.cap lam tr i ≤ c * lam + 4 * lam := by
  have h0 := h.caps lam hl i hi
  have h1 := GeneralPieces.DefGenPieces.logb_le hl
  have h2 : (0 : ℝ) ≤ lam := Nat.cast_nonneg _
  have h3 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  have h4 : 4 * ρ * lam ≤ 4 * 1 * lam := mul_le_mul_of_nonneg_right (by linarith [h.rho_lt]) h2
  have h5 : (c : ℝ) * Real.logb 2 (2 * lam) ≤ c * lam := mul_le_mul_of_nonneg_left h1 h3
  have h6 : ((D.cap lam false i + D.cap lam true i : ℕ) : ℝ) ≤ ((c * lam + 4 * lam : ℕ) : ℝ) := by
    push_cast at h0 ⊢
    linarith
  have h7 : D.cap lam false i + D.cap lam true i ≤ c * lam + 4 * lam := by exact_mod_cast h6
  cases tr <;> omega
end Data.Is
end PiecesCounted
