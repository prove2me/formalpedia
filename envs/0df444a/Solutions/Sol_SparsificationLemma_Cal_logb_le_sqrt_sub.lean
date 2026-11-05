-- Prove2me | solution 1 for SparsificationLemma.Cal.logb_le_sqrt_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:31:21.009248+00:00
-- url     : https://prove2.me/submissions/a7894e96-a84c-4e97-ba92-ee1929c04004

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
theorem _root_.solution {x : ℝ} (hx : 128 ≤ x) : Real.logb 2 x ≤ Real.sqrt x - 9 / 8 := by
  have hx0 : 0 < x := by linarith
  have hs11 : 11 ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by linarith)
  have hs0 : 0 < Real.sqrt x := by linarith
  have hL1 := Real.log_two_gt_d9
  have hL0 : 0 < Real.log 2 := by linarith
  have h1 : Real.log (Real.sqrt x / 16) ≤ Real.sqrt x / 16 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h2 : Real.log (Real.sqrt x / 16) = Real.log (Real.sqrt x) - 4 * Real.log 2 := by
    rw [Real.log_div hs0.ne' (by norm_num), show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have h3 : Real.log x = 2 * Real.log (Real.sqrt x) := by rw [Real.log_sqrt hx0.le]; ring
  rw [Real.logb, div_le_iff₀ hL0, h3]
  have h5 : 0 ≤ (Real.log 2 - 0.693) * (Real.sqrt x - 73 / 8) := mul_nonneg (by linarith) (by linarith)
  nlinarith
end SparsificationLemma.Cal
