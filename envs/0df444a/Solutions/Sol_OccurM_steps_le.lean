-- Prove2me | solution 1 for OccurM.steps_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:08:22.022195+00:00
-- url     : https://prove2.me/submissions/de4925d5-fc5e-43c8-b540-9c3231764088

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
import Theorems.Thm_OccurM_pow_le_timeClauses
import Theorems.Thm_OccurM_timeClauses_mono
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_VariableBound_Rename_poly_le
import Theorems.Thm_VariableBound_Rename_poly_mono
import Theorems.Thm_VariableBound_Rename_steps_split


set_option autoImplicit false
section
section
open OccurM
open MainTheoremForms ClausesOccur VariableBound.Paper
variable {α : ℝ} {k m : ℕ}
namespace OccurM
theorem _root_.solution (q G : ℕ) {E a : ℕ} (hE : (E : ℝ) ≤ G * expClauses α k m) (hX : 1 ≤ expClauses α k m) (ha : 1 ≤ a) :
    q * (a + 2 ^ E + 1) ^ q ≤ timeClauses α (stepsC q G) k m + stepsC q G * a ^ stepsC q G := by
  refine (VariableBound.Rename.steps_split q a 0 E).trans ?_
  rw [add_comm]
  refine Nat.add_le_add ?_ ((VariableBound.Rename.poly_le q ha).trans (VariableBound.Rename.poly_mono (le_max_right _ _) ha))
  have hb : 0 + 2 ^ E + 1 ≤ 2 ^ (E + 1) := by
    have := Nat.one_le_two_pow (n := E)
    rw [pow_succ]
    omega
  have h1 : 2 * q * (0 + 2 ^ E + 1) ^ (2 * q) ≤ 2 ^ (2 * q + (E + 1) * (2 * q)) := by
    calc 2 * q * (0 + 2 ^ E + 1) ^ (2 * q) ≤ 2 ^ (2 * q) * (2 ^ (E + 1)) ^ (2 * q) :=
          Nat.mul_le_mul Nat.lt_two_pow_self.le (Nat.pow_le_pow_left hb _)
      _ = 2 ^ (2 * q + (E + 1) * (2 * q)) := by rw [← pow_mul, ← pow_add]
  refine h1.trans ((pow_le_timeClauses (C := 4 * q + 2 * q * G) ?_).trans (timeClauses_mono (le_max_left _ _) (by linarith)))
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  push_cast
  nlinarith [mul_nonneg hq (sub_nonneg.2 hX), mul_nonneg hq (sub_nonneg.2 hE)]
end OccurM
