-- Prove2me | solution 1 for SparsificationLemma.Cal.stSqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:14:52.002668+00:00
-- url     : https://prove2.me/submissions/86d6802d-6f19-4575-85bd-c7e108667b5a

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
theorem _root_.solution : StSqrt := by
  intro x hx
  have hx0 : 0 < x := by linarith
  have h16 : 16 / x ≤ 1 / 8 := by rw [div_le_iff₀ hx0]; linarith
  have h4 := logb_le_sqrt_sub hx
  linarith
end SparsificationLemma.Cal
