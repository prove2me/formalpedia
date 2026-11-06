-- Prove2me | solution 1 for VariableBound.Net.FitL.ub_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:36:12.731193+00:00
-- url     : https://prove2.me/submissions/5ca63906-f407-4a93-9640-123885c463ff

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Definitions.Def_VariableBound_Net_Fit
import Theorems.Thm_VariableBound_Net_FitL_lg_mono
import Theorems.Thm_VariableBound_Net_FitL_lg_le_clog
import Theorems.Thm_VariableBound_Net_FitL_lg_two_mul_le

set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.FitL
open Groundwork PaddedDescent.F
open PaddedDescent.F.Mark (qv WfL occ nProf)
open ClauseBound.ParityChecks (LD)
namespace VariableBound.Net.FitL
theorem _root_.solution (k K n : ℕ) {Δ : ℕ} (hΔ : 2 ≤ Δ) :
    6 * (k : ℝ) * (n + lg (2 * Δ)) + 28 * k * n * lg (96 * Δ * lg (2 * Δ)) + 2 * ((3 * K ^ 8 : ℕ) : ℝ) ^ 2 ≤ ((UbD k K n Δ : ℕ) : ℝ) := by
  have hΔ' : (2 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  have h1 := lg_two_mul_le Δ
  have h0 : 0 < lg (2 * Δ) := Real.logb_pos (by norm_num) (by linarith)
  have h2 : lg (96 * Δ * lg (2 * Δ)) ≤ Nat.clog 2 (96 * Δ * LD Δ) := by
    refine le_trans (lg_mono (by positivity) ?_) (lg_le_clog _)
    push_cast
    gcongr
  unfold UbD
  push_cast
  gcongr
end VariableBound.Net.FitL
