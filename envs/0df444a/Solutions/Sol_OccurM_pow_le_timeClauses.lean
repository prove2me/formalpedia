-- Prove2me | solution 1 for OccurM.pow_le_timeClauses
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:56:26.23624+00:00
-- url     : https://prove2.me/submissions/d0cb2a46-19c7-4bdf-ba07-b1e4e2c035d8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClausesOccurStatement
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Paper_Rename_Time
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_OccurM_Arith

set_option autoImplicit false
section
section
open OccurM
open MainTheoremForms ClausesOccur VariableBound.Paper
variable {α : ℝ} {k m : ℕ}
namespace OccurM
theorem _root_.solution {e C : ℕ} (h : (e : ℝ) ≤ C * expClauses α k m) : 2 ^ e ≤ timeClauses α C k m := by
  unfold timeClauses
  refine Nat.le_floor ?_
  push_cast
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le one_le_two h
end OccurM
