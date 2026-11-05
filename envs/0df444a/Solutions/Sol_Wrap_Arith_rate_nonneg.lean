-- Prove2me | solution 1 for Wrap.Arith.rate_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:53:39.382445+00:00
-- url     : https://prove2.me/submissions/814b343d-da6a-4543-b3ab-b5d614e89538

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

set_option autoImplicit false
section
section
open Wrap
open MainTheoremForms
open Wrap.Arith
namespace Wrap.Arith
theorem _root_.solution (n : ℕ) : 0 ≤ SatK.rN 1 (1 / 2) n := by
  obtain ⟨-, h2⟩ := lg_add_four_facts n
  rw [rate_eq]
  exact div_nonneg (by linarith) (Real.sqrt_nonneg _)
end Wrap.Arith
