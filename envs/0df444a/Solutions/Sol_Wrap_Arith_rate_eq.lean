-- Prove2me | solution 1 for Wrap.Arith.rate_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:35:00.955917+00:00
-- url     : https://prove2.me/submissions/aec204fb-7305-4fdd-a7cc-ef79663ee6dd

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

set_option autoImplicit false
section
section
open Wrap
open MainTheoremForms
open Wrap.Arith
namespace Wrap.Arith
theorem _root_.solution (n : ℕ) : SatK.rN 1 (1 / 2) n = lg (lg ((n : ℝ) + 4)) / Real.sqrt (lg ((n : ℝ) + 4)) := by
  unfold SatK.rN
  rw [← Real.sqrt_eq_rpow, pow_one]
  rfl
end Wrap.Arith
