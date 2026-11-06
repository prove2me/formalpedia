-- Prove2me | solution 1 for QueryMachines.Bridge.Proof.le_ceilMul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:56:56.554365+00:00
-- url     : https://prove2.me/submissions/f48748e1-8365-44ac-b2c6-4704848e7881

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
theorem _root_.solution {a b : ℕ} (hb : 0 < b) (n : ℕ) : min ((a : ℝ) / b) 1 * n ≤ ceilMul a b n := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  unfold ceilMul
  split
  · calc min ((a : ℝ) / b) 1 * n ≤ 1 * n := mul_le_mul_of_nonneg_right (min_le_right _ _) hn
      _ = n := one_mul _
  · have h1 : a * n ≤ b * ((a * n + b - 1) / b) := by
      have := Nat.div_add_mod (a * n + b - 1) b
      have := Nat.mod_lt (a * n + b - 1) hb
      omega
    have h2 : (a : ℝ) * n ≤ b * ((a * n + b - 1) / b : ℕ) := by exact_mod_cast h1
    calc min ((a : ℝ) / b) 1 * n ≤ (a : ℝ) / b * n := mul_le_mul_of_nonneg_right (min_le_left _ _) hn
      _ = (a : ℝ) * n / b := by ring
      _ ≤ _ := by rw [div_le_iff₀ hb']; linarith
end QueryMachines.Bridge.Proof
