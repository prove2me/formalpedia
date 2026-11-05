-- Prove2me | solution 1 for SparsificationLemma.Cal.alphaC_le_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:30:56.585508+00:00
-- url     : https://prove2.me/submissions/f29158d6-25a7-4879-87c6-340cdd96310a

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
import Theorems.Thm_SparsificationLemma_Cal_clog_lt_logb_add_one
import Theorems.Thm_SparsificationLemma_Cal_stAlpha
import Theorems.Thm_SparsificationLemma_Cal_stSqrt


set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Cal
namespace SparsificationLemma.Cal
theorem _root_.solution {k : ℕ} {ε : ℚ} (hk : 3 ≤ k) (h0 : 0 < ε) (h1 : ε ≤ 1) :
    32 * (alphaC k ε : ℝ) ≤ 2 * ((xC k ε : ℚ) : ℝ) * Real.sqrt ((xC k ε : ℚ) : ℝ) := by
  obtain ⟨hx, -, -, -, hhi⟩ := stAlpha k ε hk h0 h1
  have hxR : (128 : ℝ) ≤ ((xC k ε : ℚ) : ℝ) := by exact_mod_cast hx
  have hhiR : 32 * (alphaC k ε : ℝ) ≤ 2 * ((xC k ε : ℚ) : ℝ) * (logC k ε : ℝ) + 32 := by exact_mod_cast hhi
  have hlt : (logC k ε : ℝ) < Real.logb 2 ((xC k ε : ℚ) : ℝ) + 1 := clog_lt_logb_add_one (by linarith)
  have hsq := stSqrt _ hxR
  generalize ((xC k ε : ℚ) : ℝ) = x at *
  have hx0 : 0 < x := by linarith
  have h16 : x * (16 / x) = 16 := by field_simp
  nlinarith
end SparsificationLemma.Cal
