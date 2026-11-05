-- Prove2me | solution 1 for PairsToBound.theBoundIncreasesWithTheWidth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:23:26.283247+00:00
-- url     : https://prove2.me/submissions/f641486f-a0bf-4d6c-8223-9d12fc89e4fb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Defs
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Printed_VariablesA_StepSparsify
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_PairsToBound_Arith
import Theorems.Thm_PairsToBound_expN_mono
import Theorems.Thm_PairsToBound_expVariablesA_mono

set_option autoImplicit false
section
section
open PairsToBound
open MainTheoremForms VariableBound.Paper
namespace PairsToBound
theorem _root_.solution : TheBoundIncreasesWithTheWidth :=
  ⟨fun C _ _ _ hn h => Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_left (expN_mono hn h) (Nat.cast_nonneg C))),
   fun C _ _ _ _ hk h he he1 => Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_left (expVariablesA_mono hk h he he1) (Nat.cast_nonneg C)))⟩
end PairsToBound
