-- Prove2me | solution 1 for SparsificationLemma.Cal.two_logb_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:14:53.052536+00:00
-- url     : https://prove2.me/submissions/a24215d1-d2e8-46a7-b797-c7044e5acb54

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Cal_Defs
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Cal_Real
import Theorems.Thm_SparsificationLemma_Cal_logb_le_sqrt_sub

set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Cal
namespace SparsificationLemma.Cal
theorem _root_.solution {x : ℝ} (hx : 128 ≤ x) : 2 * Real.logb 2 x ≤ x := by
  have hx0 : 0 ≤ x := by linarith
  have hs11 : 11 ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by linarith)
  have hs2 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0
  have h4 := logb_le_sqrt_sub hx
  nlinarith
end SparsificationLemma.Cal
