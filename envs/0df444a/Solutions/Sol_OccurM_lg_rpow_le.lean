-- Prove2me | solution 1 for OccurM.lg_rpow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:56:24.201203+00:00
-- url     : https://prove2.me/submissions/42c7dabd-d202-4dc2-a45c-898c8533e6b1

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
import Theorems.Thm_VariableBound_Paper_one_le_lg


set_option autoImplicit false
section
section
open OccurM
open MainTheoremForms ClausesOccur VariableBound.Paper
variable {α : ℝ} {k m : ℕ}
namespace OccurM
theorem _root_.solution (h1 : α ≤ 1) (hm : 2 ≤ m) : lg m ^ α ≤ lg m := by
  have h := Real.rpow_le_rpow_of_exponent_le (one_le_lg hm) h1
  rwa [Real.rpow_one] at h
end OccurM
