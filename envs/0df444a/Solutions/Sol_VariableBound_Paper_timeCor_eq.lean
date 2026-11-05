-- Prove2me | solution 1 for VariableBound.Paper.timeCor_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:42:22.274853+00:00
-- url     : https://prove2.me/submissions/bbab830e-c28f-4b8c-b15c-d67699674f75

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
theorem _root_.solution (C k m n : ℕ) : timeCor C k m n = timeMin C k m n := by
  have hmono : Monotone fun x : ℝ => (2 : ℝ) ^ ((C : ℝ) * x) := fun x y hxy =>
    Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_left hxy (Nat.cast_nonneg C))
  unfold timeCor timeMin
  rw [hmono.map_min]
end VariableBound.Paper
