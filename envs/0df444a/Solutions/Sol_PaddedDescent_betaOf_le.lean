-- Prove2me | solution 1 for PaddedDescent.betaOf_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:10:43.200652+00:00
-- url     : https://prove2.me/submissions/13594dfb-c3e6-4ddc-99c3-ed9cbe395152

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Seq
import Definitions.Def_SparsifyWidthK_Thresholds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Definitions.Def_PaddedDescent_Choice
import Theorems.Thm_PaddedDescent_add_seven_le

set_option autoImplicit false
section
section
set_option exponentiation.threshold 1024
open PaddedDescent
open WidthK (theta bsum leafC)
open WidthK.Thresholds
namespace PaddedDescent
theorem _root_.solution (s : ℕ) : betaOf s ≤ 49 * 2 ^ (2 * s) := by
  calc betaOf s ≤ (7 * 2 ^ s) ^ 2 := Nat.pow_le_pow_left (add_seven_le s) 2
    _ = 49 * 2 ^ (2 * s) := by rw [mul_pow, ← pow_mul, Nat.mul_comm s 2]; norm_num
end PaddedDescent
