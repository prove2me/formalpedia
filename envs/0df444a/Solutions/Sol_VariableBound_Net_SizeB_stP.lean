-- Prove2me | solution 1 for VariableBound.Net.SizeB.stP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:40:47.592147+00:00
-- url     : https://prove2.me/submissions/d93336be-3b61-4a0d-ab58-1a8d22cfb986

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_VariableBound_Net_Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.List.Nodup
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Net_SizeB
import Theorems.Thm_VariableBound_Net_SizeB_mul_qv_le
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
open VariableBound VariableBound.Net VariableBound.Net.SizeB
open Groundwork Groundwork.Prog Finset PaddedDescent.F VariableBound.Net.Basic
open PaddedDescent.F.Mark (Cl qv vio WfL occ)
variable {k g n : ℕ} {D : Dat} {y : ℕ}
namespace VariableBound.Net.SizeB
theorem _root_.solution : StP := by
  intro g n Δ tb rb sb _ hsb hrb
  have hA : (0 : ℚ) ≤ 1 + Δ * (tb + 3) := by positivity
  have h0 : 0 ≤ 2 * P0 g n Δ tb rb sb := by
    unfold P0
    positivity
  have h1 : ((g : ℚ) * qv g n) ≤ n + g := by exact_mod_cast mul_qv_le g n
  have h2 : ((g : ℚ) * qv g rb) ≤ 10 * n + g := by
    have h : g * qv g rb ≤ 10 * n + g := (mul_qv_le g rb).trans (by omega)
    exact_mod_cast h
  have h3 : (PD g n Δ tb rb sb : ℚ) ≤ 2 * P0 g n Δ tb rb sb + 1 := (Nat.ceil_lt_add_one h0).le
  have h4 : (g : ℚ) * PD g n Δ tb rb sb ≤ g * (2 * P0 g n Δ tb rb sb + 1) := mul_le_mul_of_nonneg_left h3 (by positivity)
  have h5 := mul_le_mul_of_nonneg_right h1 hA
  have h6 := mul_le_mul_of_nonneg_right h2 hsb
  have h7 : (g : ℚ) * (2 * P0 g n Δ tb rb sb + 1) = 2 * ((g : ℚ) * qv g n * (1 + Δ * (tb + 3))) + 2 * ((g : ℚ) * qv g rb * sb) + g := by
    unfold P0
    ring
  push_cast
  linarith
end VariableBound.Net.SizeB
