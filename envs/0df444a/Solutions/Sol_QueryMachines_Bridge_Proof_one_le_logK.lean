-- Prove2me | solution 1 for QueryMachines.Bridge.Proof.one_le_logK
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:44:43.3312+00:00
-- url     : https://prove2.me/submissions/a273480b-5662-47a0-9972-18030d67d4a1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_ToTuring_Lib_Nat1
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Definitions.Def_CountedToPadded_Need

set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge QueryMachines.Bridge.Proof
open Groundwork PaddedDescent.F Printed CliqueLevels
namespace QueryMachines.Bridge.Proof
theorem _root_.solution {K : ℕ → ℕ} {e : ℕ → ℝ} {C₀ : ℕ} (hL : Levels K e C₀) (l : ℕ) : 1 ≤ Real.logb 2 (K l) := by
  have h2 : (2 : ℝ) ≤ K l := by exact_mod_cast hL.K_two l
  rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith), Real.rpow_one]
  exact h2
end QueryMachines.Bridge.Proof
