-- Prove2me | solution 1 for Sat3.logb_le_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:34:47.100079+00:00
-- url     : https://prove2.me/submissions/06b93924-ba2d-484d-948d-331b4345826d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatRateStatement
import Definitions.Def_PaddedDescent_Params
import Definitions.Def_ToTuring_EndLemmas
import Definitions.Def_PaddedDescent_RateLemmas
import Theorems.Thm_Sat3_add_two_le_two_pow

set_option autoImplicit false
section
section
open Sat3
open Turing
open scoped NNReal ENNReal
namespace Sat3
theorem _root_.solution (n : ℕ) :
    Real.logb 2 ((n : ℝ) + 2) ≤ (2 : ℝ) ^ (Nat.log2 (Nat.log2 n) + 2) := by
  have h1 : (n : ℝ) + 2 ≤ (2 : ℝ) ^ (Nat.log2 n + 2) := by exact_mod_cast add_two_le_two_pow n
  have h2 : (Nat.log2 n : ℝ) + 2 ≤ (2 : ℝ) ^ (Nat.log2 (Nat.log2 n) + 2) := by
    exact_mod_cast add_two_le_two_pow (Nat.log2 n)
  have h3 : Real.logb 2 ((n : ℝ) + 2) ≤ (Nat.log2 n : ℝ) + 2 := by
    rw [Real.logb_le_iff_le_rpow one_lt_two (by positivity)]
    refine h1.trans_eq ?_
    rw [← Real.rpow_natCast]
    push_cast
    rfl
  exact h3.trans h2
end Sat3
