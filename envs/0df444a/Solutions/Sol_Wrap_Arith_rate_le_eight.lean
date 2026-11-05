-- Prove2me | solution 1 for Wrap.Arith.rate_le_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:53:40.835124+00:00
-- url     : https://prove2.me/submissions/e3c4cbbf-2945-4894-b351-135dfad81f6f

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
import Theorems.Thm_Wrap_Arith_rate_eq
import Theorems.Thm_Wrap_Arith_lg_add_four_facts
import Theorems.Thm_Wrap_Arith_lg_div_sqrt_le


set_option autoImplicit false
section
section
open Wrap
open MainTheoremForms
open Wrap.Arith
namespace Wrap.Arith
theorem _root_.solution (n : ℕ) : SatK.rN 1 (1 / 2) n ≤ 8 := by
  obtain ⟨h1, -⟩ := lg_add_four_facts n
  have hw1 : 1 ≤ Real.sqrt (Real.sqrt (lg ((n : ℝ) + 4))) := Real.one_le_sqrt.2 (Real.one_le_sqrt.2 (by linarith))
  rw [rate_eq]
  exact (lg_div_sqrt_le (by linarith)).trans (div_le_self (by norm_num) hw1)
end Wrap.Arith
