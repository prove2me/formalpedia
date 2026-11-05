-- Prove2me | solution 1 for VariableBound.Net.SizeU.lg_le_lg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:29:09.678512+00:00
-- url     : https://prove2.me/submissions/e769d80b-5bf4-4c44-8fcb-1e0404d7369f

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

set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.SizeU
open Finset Groundwork AppVariables
variable {k g n nb M : ℕ} {D : Dat} {fl : Bool} {y : ℕ}
namespace VariableBound.Net.SizeU
theorem _root_.solution {x z : ℝ} (h0 : 0 ≤ x) (h : x ≤ z) (h1 : 1 ≤ z) : lg x ≤ lg z := by
  unfold lg
  rcases h0.eq_or_lt with rfl | h0
  · rw [Real.logb_zero]; exact Real.logb_nonneg (by norm_num) h1
  · exact Real.logb_le_logb_of_le (by norm_num) h0 h
end VariableBound.Net.SizeU
