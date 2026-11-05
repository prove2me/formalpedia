-- Prove2me | solution 1 for VariableBound.Paper.expM_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:16:37.245104+00:00
-- url     : https://prove2.me/submissions/a90bd964-f382-4ba6-ae07-0625ea420264

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

set_option autoImplicit false
section
section
open VariableBound VariableBound.Paper
open MainTheoremForms
namespace VariableBound.Paper
theorem _root_.solution (k m : ℕ) : expM k m = (k : ℝ) * ((m : ℝ) / Real.sqrt (lg m)) := by
  unfold expM
  ring
end VariableBound.Paper
