-- Prove2me | solution 1 for PaddedDescent.two_pow_betaOf_le_Ktop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:14:04.539781+00:00
-- url     : https://prove2.me/submissions/e1f83c8f-79b9-4cd0-86e4-e768c23b91b9

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
import Theorems.Thm_PaddedDescent_betaOf_le
import Theorems.Thm_PaddedDescent_two_pow_le_Ktop


set_option autoImplicit false
section
section
set_option exponentiation.threshold 1024
open PaddedDescent
open WidthK (theta bsum leafC)
open WidthK.Thresholds
namespace PaddedDescent
theorem _root_.solution (s : ℕ) : 2 ^ (4 * betaOf s + 10 * s + 1000) ≤ Ktop s := by
  refine two_pow_le_Ktop ?_
  have h1 := betaOf_le s
  have h2 : s + 1 ≤ 2 ^ s := Nat.lt_two_pow_self
  have h3 : 2 ^ s ≤ 2 ^ (2 * s) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 1 ≤ 2 ^ (2 * s) := Nat.one_le_two_pow
  calc 4 * betaOf s + 10 * s + 1000 ≤ 2 ^ 11 * 2 ^ (2 * s) := by omega
    _ = 2 ^ (11 + 2 * s) := by rw [← pow_add]
    _ ≤ 2 ^ depthOf s := Nat.pow_le_pow_right (by norm_num) (by unfold depthOf; omega)
end PaddedDescent
