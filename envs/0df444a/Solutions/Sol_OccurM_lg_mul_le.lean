-- Prove2me | solution 1 for OccurM.lg_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:08:26.708393+00:00
-- url     : https://prove2.me/submissions/dd5ecb6c-e8b7-4b60-9d2a-c130e5a421b6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClausesOccurStatement
import Definitions.Def_OccurM_Arith
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_Wrap_Arith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_OccurM_ArithBack
import Theorems.Thm_OccurM_sq_lg_add_two_le
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_OccurM_lg_add_two_le
import Theorems.Thm_VariableBound_Paper_lg_le_sub_one
import Theorems.Thm_VariableBound_Paper_lg_mono
import Theorems.Thm_VariableBound_Paper_lg_two
import Theorems.Thm_VariableBound_Paper_one_le_lg


set_option autoImplicit false
section
section
open OccurM
open MainTheoremForms ClausesOccur VariableBound.Paper
variable {α : ℝ} {k m : ℕ}
namespace OccurM
theorem _root_.solution (h1 : α ≤ 1) (hk : 1 ≤ k) (hm : 2 ≤ m) : lg ((k : ℝ) * m) ≤ 130 * ((k : ℝ) * m * SatM.rPow α m) := by
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hL1 : 1 ≤ lg ((m : ℝ) + 2) := by linarith [lg_mono two_pos (by linarith : (2 : ℝ) ≤ (m : ℝ) + 2), lg_two]
  have hLm : lg m ≤ lg ((m : ℝ) + 2) := lg_mono (by linarith) (by linarith)
  have hp : 0 < lg ((m : ℝ) + 2) ^ α := Real.rpow_pos_of_pos (by linarith) α
  have hpl : lg ((m : ℝ) + 2) ^ α ≤ lg ((m : ℝ) + 2) := by
    have h := Real.rpow_le_rpow_of_exponent_le hL1 h1
    rwa [Real.rpow_one] at h
  have hsplit : lg ((k : ℝ) * m) = lg k + lg m := by
    unfold lg
    exact Real.logb_mul (by linarith) (by linarith)
  have hlk : lg k ≤ k := by linarith [lg_le_sub_one hk]
  have hlk0 : 0 ≤ lg k := by
    have h := lg_mono one_pos hk1
    unfold lg at h ⊢
    rwa [Real.logb_one] at h
  have hlm0 : 0 ≤ lg m := by linarith [one_le_lg hm]
  have hL2m : lg ((m : ℝ) + 2) ≤ 2 * m := by linarith [lg_add_two_le hm, lg_le_sub_one (by omega : 1 ≤ m)]
  have ha : lg k * lg ((m : ℝ) + 2) ≤ k * (2 * m) := mul_le_mul hlk hL2m (by linarith) (by linarith)
  have hb : lg m * lg ((m : ℝ) + 2) ≤ 128 * m := (mul_le_mul_of_nonneg_right hLm (by linarith)).trans (sq_lg_add_two_le hm)
  have hkm : (m : ℝ) ≤ k * m := by nlinarith
  have hmain : lg ((k : ℝ) * m) * lg ((m : ℝ) + 2) ^ α ≤ 130 * ((k : ℝ) * m) := by
    calc lg ((k : ℝ) * m) * lg ((m : ℝ) + 2) ^ α ≤ lg ((k : ℝ) * m) * lg ((m : ℝ) + 2) := mul_le_mul_of_nonneg_left hpl (by rw [hsplit]; linarith)
      _ = lg k * lg ((m : ℝ) + 2) + lg m * lg ((m : ℝ) + 2) := by rw [hsplit]; ring
      _ ≤ 130 * ((k : ℝ) * m) := by linarith
  have e : 130 * ((k : ℝ) * m * SatM.rPow α m) = 130 * ((k : ℝ) * m) / lg ((m : ℝ) + 2) ^ α := by
    unfold SatM.rPow lg
    ring
  rw [e, le_div_iff₀ hp]
  exact hmain
end OccurM
