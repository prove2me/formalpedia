-- Prove2me | solution 1 for OccurM.sq_lg_add_two_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:01:04.974201+00:00
-- url     : https://prove2.me/submissions/226e9e8a-efa8-4807-a7d9-e5c9461929f0

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
import Theorems.Thm_VariableBound_Paper_lg_mono
import Theorems.Thm_VariableBound_Paper_lg_two
import Theorems.Thm_Wrap_Arith_lg_le_fourth_root


set_option autoImplicit false
section
section
open OccurM
open MainTheoremForms ClausesOccur VariableBound.Paper
variable {α : ℝ} {k m : ℕ}
namespace OccurM
theorem _root_.solution (hm : 2 ≤ m) : lg ((m : ℝ) + 2) * lg ((m : ℝ) + 2) ≤ 128 * m := by
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hy : (0 : ℝ) < (m : ℝ) + 2 := by linarith
  have h8 := Wrap.Arith.lg_le_fourth_root hy
  have hl0 : 0 ≤ lg ((m : ℝ) + 2) := by linarith [lg_mono two_pos (by linarith : (2 : ℝ) ≤ (m : ℝ) + 2), lg_two]
  have hs0 : 0 ≤ Real.sqrt (Real.sqrt ((m : ℝ) + 2)) := Real.sqrt_nonneg _
  have hss : Real.sqrt (Real.sqrt ((m : ℝ) + 2)) * Real.sqrt (Real.sqrt ((m : ℝ) + 2)) = Real.sqrt ((m : ℝ) + 2) := Real.mul_self_sqrt (Real.sqrt_nonneg _)
  have hle : Real.sqrt ((m : ℝ) + 2) ≤ (m : ℝ) + 2 := Real.sqrt_le_iff.2 ⟨hy.le, by nlinarith⟩
  have hmul := mul_le_mul h8 h8 hl0 (by positivity)
  nlinarith
end OccurM
