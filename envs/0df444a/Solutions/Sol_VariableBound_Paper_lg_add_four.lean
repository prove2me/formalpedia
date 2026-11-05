-- Prove2me | solution 1 for VariableBound.Paper.lg_add_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:50:36.200892+00:00
-- url     : https://prove2.me/submissions/5cc348a3-2f39-4298-87be-8f8df1b5f431

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainTheoremFormsStatement
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Definitions.Def_VariableBound_Paper_Arith
import Theorems.Thm_VariableBound_Paper_lg_mono
import Theorems.Thm_VariableBound_Paper_lg_two
import Theorems.Thm_VariableBound_Paper_lg_two_mul

set_option autoImplicit false
section
section
open VariableBound VariableBound.Paper
open MainTheoremForms
namespace VariableBound.Paper
theorem _root_.solution {n : ℕ} (hn : 4 ≤ n) :
    2 ≤ lg n ∧ lg n ≤ lg ((n : ℝ) + 4) ∧ 1 ≤ lg (lg n) ∧ 0 ≤ lg (lg ((n : ℝ) + 4)) ∧ lg (lg ((n : ℝ) + 4)) ≤ 2 * lg (lg n) := by
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hL2 : 2 ≤ lg n := by
    have h4 : lg 4 = 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, lg_two_mul two_pos, lg_two]
      norm_num
    rw [← h4]
    exact lg_mono (by norm_num) hn4
  have hLL' : lg n ≤ lg ((n : ℝ) + 4) := lg_mono (by linarith) (by linarith)
  have hL'2 : lg ((n : ℝ) + 4) ≤ 2 * lg n := by
    have h2 : lg ((n : ℝ) + 4) ≤ lg (2 * n) := lg_mono (by linarith) (by linarith)
    have h3 := lg_two_mul (x := (n : ℝ)) (by linarith)
    linarith
  have hl1 : 1 ≤ lg (lg n) := by
    rw [← lg_two]
    exact lg_mono two_pos hL2
  have hl' : lg (lg ((n : ℝ) + 4)) ≤ 2 * lg (lg n) := by
    have h1 : lg (lg ((n : ℝ) + 4)) ≤ lg (2 * lg n) := lg_mono (by linarith) hL'2
    have h2 := lg_two_mul (x := lg n) (by linarith)
    linarith
  have hl0 : 0 ≤ lg (lg ((n : ℝ) + 4)) := by
    have : lg (lg n) ≤ lg (lg ((n : ℝ) + 4)) := lg_mono (by linarith) hLL'
    linarith
  exact ⟨hL2, hLL', hl1, hl0, hl'⟩
end VariableBound.Paper
