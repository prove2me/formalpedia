-- Prove2me | solution 1 for UniformInK.FallBack.logb_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:16:35.91246+00:00
-- url     : https://prove2.me/submissions/a959bc2f-532c-43f0-8403-a5079d73fcb8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_ClauseBound_TopN_Gen
import Definitions.Def_UniformInK_Top_FallBack

set_option autoImplicit false
section
section
open UniformInK UniformInK.FallBack
open ClauseBound.TopN.GenN
namespace UniformInK.FallBack
theorem _root_.solution (n : ℕ) : Real.logb 2 ((n : ℝ) + 4) ≤ (Nat.log 2 n : ℝ) + 3 := by
  have h1 : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have h2 : 1 ≤ 2 ^ Nat.log 2 n := Nat.one_le_two_pow
  have h3 : n + 4 ≤ 2 ^ (Nat.log 2 n + 3) := by
    rw [pow_succ] at h1
    rw [pow_add]
    omega
  have h4 : (n : ℝ) + 4 ≤ (2 : ℝ) ^ (Nat.log 2 n + 3) := by exact_mod_cast h3
  rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity)]
  calc (n : ℝ) + 4 ≤ (2 : ℝ) ^ (Nat.log 2 n + 3) := h4
    _ = (2 : ℝ) ^ ((Nat.log 2 n : ℝ) + 3) := by
      rw [← Real.rpow_natCast]
      push_cast
      rfl
end UniformInK.FallBack
