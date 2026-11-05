-- Prove2me | solution 1 for PaddedDescent.decay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:56:23.359386+00:00
-- url     : https://prove2.me/submissions/43615b26-1569-4e54-93cf-14835b2b0ee9

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
import Theorems.Thm_PaddedDescent_decay_aux

set_option autoImplicit false
section
section
set_option exponentiation.threshold 1024
open PaddedDescent
open WidthK (theta bsum leafC)
open WidthK.Thresholds
namespace PaddedDescent
theorem _root_.solution {C : ℕ} (hC : C ≤ 2 ^ 10) (s : ℕ) :
    8963 ^ depthOf s * (C * (s + 8) ^ 6 * 2 ^ s) ≤ 10000 ^ depthOf s := by
  rw [depthOf]
  have h : (s + 8) ^ 6 ≤ (s + 2 ^ 15) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  exact le_trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul hC h))) (decay_aux s)
end PaddedDescent
