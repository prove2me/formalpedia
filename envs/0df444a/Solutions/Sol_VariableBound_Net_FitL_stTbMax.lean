-- Prove2me | solution 1 for VariableBound.Net.FitL.stTbMax
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:36:03.385193+00:00
-- url     : https://prove2.me/submissions/8a185a55-c2e6-4595-b4ba-883acd4cb810

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
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.FitL
open Groundwork PaddedDescent.F
open PaddedDescent.F.Mark (qv WfL occ nProf)
open ClauseBound.ParityChecks (LD)
namespace VariableBound.Net.FitL
theorem _root_.solution : StTbMax := by
  intro n Δ m tb hm hmΔ h
  have h1 : lg m ≤ Nat.clog 2 (Δ * n) := (lg_mono (by exact_mod_cast hm) (by exact_mod_cast hmΔ)).trans (lg_le_clog (Δ * n))
  have h2 := lg_two_mul_le Δ
  have h3 : (tb : ℝ) ≤ ((tbMax n Δ : ℕ) : ℝ) := by
    unfold tbMax
    push_cast
    linarith
  exact_mod_cast h3
end VariableBound.Net.FitL
