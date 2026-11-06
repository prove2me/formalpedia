-- Prove2me | solution 1 for OccurM.timeClauses_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:56:27.180212+00:00
-- url     : https://prove2.me/submissions/2ab00e1e-0ec1-47b1-b732-ae98181dd9a6

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

set_option autoImplicit false
section
section
open OccurM
open MainTheoremForms ClausesOccur VariableBound.Paper
variable {α : ℝ} {k m : ℕ}
namespace OccurM
theorem _root_.solution {C C' : ℕ} (h : C ≤ C') (hX : 0 ≤ expClauses α k m) : timeClauses α C k m ≤ timeClauses α C' k m := by
  unfold timeClauses
  exact Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_right (by exact_mod_cast h) hX))
end OccurM
