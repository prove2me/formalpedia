-- Prove2me | solution 1 for VariableBound.Net.FitL.small_le_PbD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:36:27.43451+00:00
-- url     : https://prove2.me/submissions/e2b17150-6716-4e30-8db3-55d5f1e60db9

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
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.FitL
open Groundwork PaddedDescent.F
open PaddedDescent.F.Mark (qv WfL occ nProf)
open ClauseBound.ParityChecks (LD)
namespace VariableBound.Net.FitL
theorem _root_.solution (K n Δ : ℕ) : 2 * (qv (3 * K ^ 8) n * (1 + Δ)) ≤ PbD K n Δ := by
  unfold PbD PD
  have h : ((2 * (qv (3 * K ^ 8) n * (1 + Δ)) : ℕ) : ℚ) ≤ 2 * P0 (3 * K ^ 8) n Δ (tbMax n Δ) (10 * n) (sbMax Δ) := by
    unfold P0
    push_cast
    have a : (Δ : ℚ) ≤ Δ * (tbMax n Δ + 3) := le_mul_of_one_le_right (by positivity) (by linarith [(Nat.cast_nonneg (tbMax n Δ) : (0 : ℚ) ≤ _)])
    have b : (0 : ℚ) ≤ (qv (3 * K ^ 8) (10 * n) : ℚ) * sbMax Δ := by positivity
    have c : (qv (3 * K ^ 8) n : ℚ) * (1 + Δ) ≤ (qv (3 * K ^ 8) n : ℚ) * (1 + Δ * (tbMax n Δ + 3)) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  exact Nat.cast_le.1 (h.trans (Nat.le_ceil _))
end VariableBound.Net.FitL
