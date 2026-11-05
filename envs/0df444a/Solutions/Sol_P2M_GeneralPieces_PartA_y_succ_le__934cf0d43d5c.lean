-- Prove2me | solution 1 for P2M_GeneralPieces_PartA_y_succ_le__934cf0d43d5c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:59:00.000875+00:00
-- url     : https://prove2.me/submissions/7f788bcb-9950-43ef-a6d7-63b9fb535ee2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_LevelsStatement
import Definitions.Def_ClauseBound_Gen_PartA
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_GeneralPieces_Num_PartA
import Theorems.Thm_GeneralPieces_PartA_y_succ_le
import Theorems.Thm_GeneralPieces_PartA_K_ge_pow

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.PartA
open Finset Levels.Gen ClauseBound.Gen
namespace GeneralPieces.PartA
theorem _root_.solution (ρ : ℝ) (x₀ l : ℕ) (hρ : 1 / 2 ≤ ρ) (hx : 18 ≤ x₀) :
    y ρ x₀ (l + 1) ≤ (1 + 1 / 2 ^ (l + 2)) * y ρ x₀ l + 6 * 2 ^ l / 2 ^ (18 * (l + 1)) := by
  have h1 : (2 : ℝ) ^ (18 * (l + 1)) ≤ K x₀ l := by exact_mod_cast K_ge_pow x₀ l hx
  have h2 : 6 * 2 ^ l / (K x₀ l : ℝ) ≤ 6 * 2 ^ l / 2 ^ (18 * (l + 1)) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) h1
  linarith [y_succ_le ρ x₀ l hρ]
end GeneralPieces.PartA
