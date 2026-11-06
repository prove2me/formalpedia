-- Prove2me | solution 1 for QueryMachines.Bridge.Proof.size_le_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:56:58.548367+00:00
-- url     : https://prove2.me/submissions/c24fa9ed-1251-4fc7-af3b-dfc4769a8ecf

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
theorem _root_.solution {m : ℕ} (hm : 1 ≤ m) : (Nat.size m : ℝ) ≤ Real.logb 2 m + 1 := by
  have hs : 1 ≤ Nat.size m := Nat.size_pos.2 hm
  have h1 : 2 ^ (Nat.size m - 1) ≤ m := Nat.lt_size.1 (by omega)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h2 : ((Nat.size m - 1 : ℕ) : ℝ) ≤ Real.logb 2 m := by
    rw [Real.le_logb_iff_rpow_le one_lt_two hm', Real.rpow_natCast]
    exact_mod_cast h1
  have h3 : ((Nat.size m - 1 : ℕ) : ℝ) = (Nat.size m : ℝ) - 1 := by rw [Nat.cast_sub hs, Nat.cast_one]
  linarith
end QueryMachines.Bridge.Proof
