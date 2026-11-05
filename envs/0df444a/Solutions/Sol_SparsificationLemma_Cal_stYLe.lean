-- Prove2me | solution 1 for SparsificationLemma.Cal.stYLe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:28:01.833359+00:00
-- url     : https://prove2.me/submissions/f5e88254-0b2a-4d9a-bc4d-5098b8fcb0cf

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
import Theorems.Thm_SparsificationLemma_Cal_mul_logb_div_le

set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Cal
namespace SparsificationLemma.Cal
theorem _root_.solution : StYLe := by
  intro k α ε _ hε hX ht
  have hA : 32 * ((k : ℝ) - 1) ^ 2 = ε * (32 * ((k : ℝ) - 1) ^ 2 / ε) := by field_simp
  have h := mul_logb_div_le hε hX ht
  rw [← hA] at h
  exact h
end SparsificationLemma.Cal
