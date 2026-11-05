-- Prove2me | solution 1 for Wrap.Arith.lg_add_four_facts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:51:50.817749+00:00
-- url     : https://prove2.me/submissions/10e60c3b-bd2c-45ac-8f6c-3e1bfdedbd7f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainTheoremFormsStatement
import Definitions.Def_Wrap_Arith
import Definitions.Def_VariableBound_Paper_Arith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_Wrap_ArithRate
import Theorems.Thm_VariableBound_Paper_lg_add_four


set_option autoImplicit false
section
section
open Wrap
open MainTheoremForms
open Wrap.Arith
namespace Wrap.Arith
theorem _root_.solution (n : ℕ) : 2 ≤ lg ((n : ℝ) + 4) ∧ 1 ≤ lg (lg ((n : ℝ) + 4)) := by
  obtain ⟨h1, -, h2, -, -⟩ := VariableBound.Paper.lg_add_four (n := n + 4) (by omega)
  push_cast at h1 h2
  exact ⟨h1, h2⟩
end Wrap.Arith
