-- Prove2me | solution 1 for PairsToBound.fallBackIsWithinTheBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:14:35.67666+00:00
-- url     : https://prove2.me/submissions/47ebf849-7ed3-43c4-936c-573a0f03bf43

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
import Theorems.Thm_PairsToBound_lg_le_div_sqrt
import Theorems.Thm_PairsToBound_div_sqrt_le_base
import Theorems.Thm_PairsToBound_mul_lg_le_expN
import Theorems.Thm_PairsToBound_mul_lglg_le_expN
import Theorems.Thm_PairsToBound_div_sqrt_level_le_base
import Theorems.Thm_VariableBound_Paper_lg_add_four


set_option autoImplicit false
section
section
open PairsToBound
open MainTheoremForms VariableBound.Paper
namespace PairsToBound
theorem _root_.solution : FallBackIsWithinTheBound :=
  ⟨fun _ hn => ⟨lg_le_div_sqrt (by omega), div_sqrt_le_base hn⟩, fun _ _ hk hn => mul_lg_le_expN hk hn,
   fun _ n hn h => ⟨mul_lglg_le_expN hn h, le_mul_of_one_le_right (Nat.cast_nonneg n) (lg_add_four hn).2.2.1⟩,
   fun _ _ _ hn h => div_sqrt_level_le_base hn h⟩
end PairsToBound
