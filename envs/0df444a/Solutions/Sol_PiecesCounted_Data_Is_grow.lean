-- Prove2me | solution 1 for PiecesCounted.Data.Is.grow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:49:02.683545+00:00
-- url     : https://prove2.me/submissions/e1d5890b-960d-4f1f-87a4-14fb1bdd44b9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Definitions.Def_GeneralPieces_DefGenPieces_ToPure
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Basic
import Theorems.Thm_PiecesCounted_pow_two_mul_le
import Theorems.Thm_GeneralPieces_DefGenPieces_logb_nonneg
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.sum



set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg
namespace PiecesCounted
namespace Data.Is
theorem _root_.solution {D : Data} {ρ ρ' : ℝ} {c c' : ℕ} (h : D.Is ρ c) (hρ : ρ ≤ ρ') (hρ' : ρ' < 1) (hc : c ≤ c') : D.Is ρ' c' :=
  have hp : ∀ lam, 1 ≤ lam → (2 : ℤ) ^ (2 * lam) ^ c ≤ 2 ^ (2 * lam) ^ c' := fun _ hl => pow_le_pow_right₀ (by norm_num) (pow_two_mul_le hl hc)
  { rho_ge := h.rho_ge.trans hρ
    rho_lt := hρ'
    c_pos := h.c_pos.trans hc
    d_pos := h.d_pos
    sum := h.sum
    row := h.row
    col := h.col
    caps := fun lam hl i hi => (h.caps lam hl i hi).trans (by
      have h0 := GeneralPieces.DefGenPieces.logb_nonneg hl
      have h1 : (0 : ℝ) ≤ lam := Nat.cast_nonneg _
      have h2 : (c : ℝ) ≤ c' := by exact_mod_cast hc
      have h3 : 4 * ρ * lam ≤ 4 * ρ' * lam := mul_le_mul_of_nonneg_right (by linarith) h1
      have h4 : (c : ℝ) * Real.logb 2 (2 * lam) ≤ c' * Real.logb 2 (2 * lam) := mul_le_mul_of_nonneg_right h2 h0
      linarith)
    card := fun lam hl => (h.card lam hl).trans (pow_two_mul_le hl hc)
    size_d := fun lam hl => (h.size_d lam hl).trans_le (hp lam hl)
    size_I := fun lam hl i hi => (h.size_I lam hl i hi).trans_le (hp lam hl)
    size_A := fun lam hl i hi x y u v => (h.size_A lam hl i hi x y u v).trans_le (hp lam hl)
    size_f := fun lam hl i hi tr side z θ hθ => (h.size_f lam hl i hi tr side z θ hθ).trans_le (hp lam hl) }
end Data.Is
end PiecesCounted
