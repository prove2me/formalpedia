-- Prove2me | solution 1 for OccurM.expClauses_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:03:22.264201+00:00
-- url     : https://prove2.me/submissions/2393d4e6-94eb-48d6-9fcf-17abb481a84c

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
import Theorems.Thm_OccurM_lg_add_two_rpow_le
import Theorems.Thm_VariableBound_Paper_lg_mono
import Theorems.Thm_VariableBound_Paper_one_le_lg


set_option autoImplicit false
section
section
open OccurM
open MainTheoremForms ClausesOccur VariableBound.Paper
variable {α : ℝ} {k m : ℕ}
namespace OccurM
theorem _root_.solution (h0 : 0 ≤ α) (h1 : α ≤ 1) (k : ℕ) (hm : 2 ≤ m) : expClauses α k m ≤ 2 * ((k : ℝ) * m * SatM.rPow α m) := by
  have hl := one_le_lg hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hl2 : 0 < lg ((m : ℝ) + 2) := by linarith [lg_mono hm0 (by linarith : (m : ℝ) ≤ (m : ℝ) + 2)]
  have hp : 0 < lg m ^ α := Real.rpow_pos_of_pos (by linarith) α
  have hp2 : 0 < lg ((m : ℝ) + 2) ^ α := Real.rpow_pos_of_pos hl2 α
  have hr : 1 / lg m ^ α ≤ 2 * (1 / lg ((m : ℝ) + 2) ^ α) := by
    rw [div_le_iff₀ hp]
    have e : 2 * (1 / lg ((m : ℝ) + 2) ^ α) * lg m ^ α = 2 * lg m ^ α / lg ((m : ℝ) + 2) ^ α := by ring
    rw [e, le_div_iff₀ hp2, one_mul]
    exact lg_add_two_rpow_le h0 h1 hm
  have hkm : (0 : ℝ) ≤ (k : ℝ) * m := by positivity
  calc expClauses α k m = (k : ℝ) * m * (1 / lg m ^ α) := by unfold expClauses; ring
    _ ≤ (k : ℝ) * m * (2 * (1 / lg ((m : ℝ) + 2) ^ α)) := mul_le_mul_of_nonneg_left hr hkm
    _ = 2 * ((k : ℝ) * m * SatM.rPow α m) := by unfold SatM.rPow lg; ring
end OccurM
