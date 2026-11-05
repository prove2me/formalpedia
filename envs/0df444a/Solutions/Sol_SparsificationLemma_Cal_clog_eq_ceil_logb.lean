-- Prove2me | solution 1 for SparsificationLemma.Cal.clog_eq_ceil_logb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:14:54.216747+00:00
-- url     : https://prove2.me/submissions/bbe0e040-7f61-4f2e-8855-42aa0708430c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Cal_Defs
import Definitions.Def_SparsificationLemma_Cal_Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Cal_Alpha
import Theorems.Thm_SparsificationLemma_Cal_logb_le_clog
import Theorems.Thm_SparsificationLemma_Cal_clog_lt_logb_add_one

set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Cal
namespace SparsificationLemma.Cal
theorem _root_.solution {x : ℚ} (hx : 1 ≤ x) : ((Nat.clog 2 ⌈x⌉₊ : ℕ) : ℤ) = ⌈Real.logb 2 (x : ℝ)⌉ := by
  symm
  rw [Int.ceil_eq_iff]
  have h1 := logb_le_clog (lt_of_lt_of_le one_pos hx)
  have h2 := clog_lt_logb_add_one hx
  constructor
  · push_cast; linarith
  · push_cast; exact h1
end SparsificationLemma.Cal
