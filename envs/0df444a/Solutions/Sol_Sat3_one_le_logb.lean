-- Prove2me | solution 1 for Sat3.one_le_logb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:28:36.989869+00:00
-- url     : https://prove2.me/submissions/15b3d752-8ee7-44a2-a551-ea49fe25d421

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatRateStatement
import Definitions.Def_PaddedDescent_Params
import Definitions.Def_ToTuring_EndLemmas
import Definitions.Def_PaddedDescent_RateLemmas

set_option autoImplicit false
section
section
open Sat3
open Turing
open scoped NNReal ENNReal
namespace Sat3
theorem _root_.solution (n : ℕ) : (1 : ℝ) ≤ Real.logb 2 ((n : ℝ) + 2) := by
  rw [Real.le_logb_iff_rpow_le one_lt_two (by positivity)]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  norm_num
end Sat3
