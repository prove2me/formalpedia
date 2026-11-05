-- Prove2me | solution 1 for Wrap.Arith.half_lt_log_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:00:57.5822+00:00
-- url     : https://prove2.me/submissions/58d2607f-bb43-4ee5-8e81-2697ed004b70

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
theorem _root_.solution : (1 : ℝ) / 2 < Real.log 2 := by
  linarith [Real.log_two_gt_d9]
end Wrap.Arith
