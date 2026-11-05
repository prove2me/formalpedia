-- Prove2me | solution 1 for UniformInK.FallBack.inv_le_rN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:16:36.926198+00:00
-- url     : https://prove2.me/submissions/54b94ed6-50f2-4d26-bdc9-6aa034bb321a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_ClauseBound_TopN_Gen
import Definitions.Def_UniformInK_Top_FallBack
import Theorems.Thm_ClauseBound_TopN_GenN_one_le_loglog
import Theorems.Thm_ClauseBound_TopN_GenN_two_le_log


set_option autoImplicit false
section
section
open UniformInK UniformInK.FallBack
open ClauseBound.TopN.GenN
namespace UniformInK.FallBack
theorem _root_.solution {α : ℝ} (ha1 : α ≤ 1) (n : ℕ) : 1 / Real.logb 2 ((n : ℝ) + 4) ≤ SatK.rN 1 α n := by
  unfold SatK.rN
  have hL := two_le_log n
  have hLL := one_le_loglog n
  have hs : Real.logb 2 ((n : ℝ) + 4) ^ α ≤ Real.logb 2 ((n : ℝ) + 4) := by
    calc Real.logb 2 ((n : ℝ) + 4) ^ α ≤ Real.logb 2 ((n : ℝ) + 4) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) ha1
      _ = Real.logb 2 ((n : ℝ) + 4) := Real.rpow_one _
  have hp : 0 < Real.logb 2 ((n : ℝ) + 4) ^ α := Real.rpow_pos_of_pos (by linarith) _
  rw [pow_one]
  exact div_le_div₀ (by linarith) hLL hp hs
end UniformInK.FallBack
