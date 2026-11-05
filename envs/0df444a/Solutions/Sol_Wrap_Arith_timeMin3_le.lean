-- Prove2me | solution 1 for Wrap.Arith.timeMin3_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:18:12.567223+00:00
-- url     : https://prove2.me/submissions/ab4ab78d-b3b5-432d-812e-4df26d245973

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainTheoremFormsStatement
import Definitions.Def_VariableBound_Paper_Arith
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Definitions.Def_Wrap_Arith

set_option autoImplicit false
section
section
open Wrap
open MainTheoremForms
open Wrap.Arith
namespace Wrap.Arith
theorem _root_.solution (C m n : ℕ) : (timeMin3 C m n : ℝ) ≤ (2 : ℝ) ^ ((C : ℝ) * ((n : ℝ) * lg (lg n) / Real.sqrt (lg n))) := by
  unfold timeMin3
  refine (Nat.floor_le (by positivity)).trans ?_
  exact Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_left (min_le_right _ _) (Nat.cast_nonneg C))
end Wrap.Arith
