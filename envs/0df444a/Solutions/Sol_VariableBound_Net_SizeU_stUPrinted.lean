-- Prove2me | solution 1 for VariableBound.Net.SizeU.stUPrinted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:30:32.515825+00:00
-- url     : https://prove2.me/submissions/a830e83a-f998-4ec3-9dfa-b18cd1c823b7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_VariableBound_Net_Tests
import Definitions.Def_VariableBound_Params_Ineq
import Definitions.Def_ClauseBound_ParityChecks_Binom
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Net_SizeU
import Theorems.Thm_VariableBound_Ineq_two_le_lg


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.SizeU
open Finset Groundwork AppVariables
variable {k g n nb M : ℕ} {D : Dat} {fl : Bool} {y : ℕ}
namespace VariableBound.Net.SizeU
theorem _root_.solution (h : StU) : StUPrinted := by
  intro k g n Δ nb M D fl y hg hS hM hadm
  have h1 := h k g n Δ nb M D fl y hg hS hadm
  have hl := Ineq.two_le_lg hS.two
  have hΔ : (2 : ℝ) ≤ Δ := by exact_mod_cast hS.two
  have hL : 0 ≤ lg (96 * Δ * lg (2 * Δ)) := Real.logb_nonneg (by norm_num) (by nlinarith)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hk : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
  have hM' : (M : ℝ) ≤ 14 * n := by exact_mod_cast hM
  have e1 : ((k - 1 : ℕ) : ℝ) * (n + lg (2 * Δ)) ≤ k * (n + lg (2 * Δ)) := mul_le_mul_of_nonneg_right hk (by linarith)
  have e2 : (k : ℝ) * M * lg (96 * Δ * lg (2 * Δ)) ≤ k * (14 * n) * lg (96 * Δ * lg (2 * Δ)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM' hk0) hL
  linarith
end VariableBound.Net.SizeU
