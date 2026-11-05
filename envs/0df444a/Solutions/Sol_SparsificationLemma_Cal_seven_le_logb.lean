-- Prove2me | solution 1 for SparsificationLemma.Cal.seven_le_logb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:32:45.645744+00:00
-- url     : https://prove2.me/submissions/02e1740d-71eb-43bc-a337-f620c604c12b

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

set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Cal
namespace SparsificationLemma.Cal
theorem _root_.solution {x : ℝ} (hx : 128 ≤ x) : 7 ≤ Real.logb 2 x := by
  have h : Real.logb 2 128 = 7 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    norm_num
  rw [← h]
  exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) hx
end SparsificationLemma.Cal
