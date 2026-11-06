-- Prove2me | solution 1 for QueryMachines.Bridge.Proof.ceilMul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:56:57.536281+00:00
-- url     : https://prove2.me/submissions/7499d06f-b7a9-42bd-bce6-71982bd083b5

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
theorem _root_.solution {a b : ℕ} (hb : 0 < b) (n : ℕ) : (ceilMul a b n : ℝ) ≤ min ((a : ℝ) / b) 1 * n + 1 := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  unfold ceilMul
  split
  · rename_i h
    have h1 : (1 : ℝ) ≤ (a : ℝ) / b := by rw [le_div_iff₀ hb', one_mul]; exact_mod_cast h
    rw [min_eq_right h1]; linarith
  · rename_i h
    have h1 : (a : ℝ) / b ≤ 1 := by rw [div_le_iff₀ hb', one_mul]; exact_mod_cast (not_le.1 h).le
    rw [min_eq_left h1]
    have h2 : (((a * n + b - 1) / b : ℕ) : ℝ) ≤ ((a * n + b - 1 : ℕ) : ℝ) / b := Nat.cast_div_le
    have h3 : ((a * n + b - 1 : ℕ) : ℝ) ≤ (a : ℝ) * n + b := by exact_mod_cast Nat.sub_le _ _
    have h4 : ((a : ℝ) * n + b) / b = (a : ℝ) / b * n + 1 := by field_simp
    calc _ ≤ ((a * n + b - 1 : ℕ) : ℝ) / b := h2
      _ ≤ ((a : ℝ) * n + b) / b := div_le_div_of_nonneg_right h3 hb'.le
      _ = _ := h4
end QueryMachines.Bridge.Proof
