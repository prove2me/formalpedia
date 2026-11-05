-- Prove2me | solution 1 for VariableBound.Paper.two_sqrt_lg_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:16:17.899347+00:00
-- url     : https://prove2.me/submissions/144841a4-d593-4a36-a9b9-2a09eccc9b14

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
import Theorems.Thm_VariableBound_Paper_lg_le_sub_one

set_option autoImplicit false
section
section
open VariableBound VariableBound.Paper
open MainTheoremForms
namespace VariableBound.Paper
theorem _root_.solution {m : ℕ} (hm : 1 ≤ m) : 2 * Real.sqrt (lg m) ≤ m := by
  have h1 := lg_le_sub_one hm
  have h2 : Real.sqrt (lg m) ≤ (m : ℝ) / 2 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    nlinarith [sq_nonneg ((m : ℝ) - 2)]
  linarith
end VariableBound.Paper
