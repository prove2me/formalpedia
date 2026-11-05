-- Prove2me | solution 1 for VariableBound.Paper.two_le_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:51:46.435555+00:00
-- url     : https://prove2.me/submissions/02d125d1-6a21-49ae-a0d9-74ba024406e8

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
import Theorems.Thm_VariableBound_Paper_two_sqrt_lg_le
import Theorems.Thm_VariableBound_Paper_lg_add_four

set_option autoImplicit false
section
section
open VariableBound VariableBound.Paper
open MainTheoremForms
namespace VariableBound.Paper
theorem _root_.solution {n : ℕ} (hn : 4 ≤ n) : 2 ≤ (n : ℝ) * lg (lg n) / Real.sqrt (lg n) := by
  obtain ⟨hL2, -, hl1, -, -⟩ := lg_add_four hn
  have hs : 0 < Real.sqrt (lg n) := Real.sqrt_pos.2 (by linarith)
  have h2 := two_sqrt_lg_le (m := n) (by omega)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [le_div_iff₀ hs]
  nlinarith
end VariableBound.Paper
