-- Prove2me | solution 1 for UniformInK.fallBack_rN_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:24:53.877326+00:00
-- url     : https://prove2.me/submissions/9972b202-e0e0-4a61-a9ca-35807cba51d3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_ClauseBound_TopN_Gen
import Definitions.Def_UniformInK_Top_FallBack
import Theorems.Thm_UniformInK_FallBack_logb_le
import Theorems.Thm_UniformInK_FallBack_inv_le_rN
import Theorems.Thm_ClauseBound_TopN_GenN_two_le_log


set_option autoImplicit false
section
section
open UniformInK
open ClauseBound.TopN.GenN UniformInK.FallBack
namespace UniformInK
theorem _root_.solution {α : ℝ} (ha1 : α ≤ 1) : FallBack (SatK.rN 1 α) := by
  intro B
  refine ⟨B + 4, fun k n hk _ hlog => ?_⟩
  have hL := two_le_log n
  have hk1 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hk)
  have hlog' : (Nat.log 2 n : ℝ) ≤ (B : ℝ) * (k : ℝ) ^ 2 := by exact_mod_cast hlog.le
  have hLk : Real.logb 2 ((n : ℝ) + 4) ≤ ((B + 4 : ℕ) : ℝ) * (k : ℝ) ^ 2 := by
    push_cast
    nlinarith [logb_le n]
  calc (1 : ℝ) = Real.logb 2 ((n : ℝ) + 4) * (1 / Real.logb 2 ((n : ℝ) + 4)) := by
        rw [mul_one_div, div_self (by linarith)]
    _ ≤ ((B + 4 : ℕ) : ℝ) * (k : ℝ) ^ 2 * SatK.rN 1 α n :=
        mul_le_mul hLk (inv_le_rN ha1 n) (by positivity) (by positivity)
end UniformInK
