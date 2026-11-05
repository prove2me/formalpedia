-- Prove2me | solution 1 for Sat3.rateBound_anti
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:33:40.260932+00:00
-- url     : https://prove2.me/submissions/d873ab1e-fb18-4df4-945b-ae37a959eee9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatRateStatement
import Definitions.Def_PaddedDescent_Params
import Definitions.Def_ToTuring_EndLemmas
import Definitions.Def_PaddedDescent_RateLemmas
import Theorems.Thm_Sat3_one_le_logb
import Theorems.Thm_Sat3_logb_rpow_pos

set_option autoImplicit false
section
section
open Sat3
open Turing
open scoped NNReal ENNReal
namespace Sat3
theorem _root_.solution (C : ℕ) {c c' : ℝ} (h : c' ≤ c) (n : ℕ) : rateBound C c n ≤ rateBound C c' n := by
  apply Nat.floor_le_floor
  have h1 : Real.logb 2 ((n : ℝ) + 2) ^ c' ≤ Real.logb 2 ((n : ℝ) + 2) ^ c :=
    Real.rpow_le_rpow_of_exponent_le (one_le_logb n) h
  have h2 := logb_rpow_pos n c'
  gcongr
  exact one_le_two
end Sat3
