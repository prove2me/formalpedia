-- Prove2me | solution 1 for PaddedDescent.leafC_tauOf_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:56:58.554245+00:00
-- url     : https://prove2.me/submissions/5dbf54d6-fbed-46f1-be7c-8c9f371b284c

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
import Theorems.Thm_PaddedDescent_theta_tauOf_le

set_option autoImplicit false
section
section
set_option exponentiation.threshold 1024
open PaddedDescent
open WidthK (theta bsum leafC)
open WidthK.Thresholds
namespace PaddedDescent
theorem _root_.solution (k s : ℕ) : leafC (tauOf s) k ≤ 2 * (k * 2 ^ ((4 * s + 17) * 2 ^ k)) := by
  rw [leafC]
  refine Nat.mul_le_mul_left _ ?_
  calc ∑ j ∈ Finset.range k, theta (tauOf s) j ≤ ∑ _j ∈ Finset.range k, 2 ^ ((4 * s + 17) * 2 ^ k) :=
        Finset.sum_le_sum fun j hj => theta_tauOf_le (Finset.mem_range.1 hj) s
    _ = k * 2 ^ ((4 * s + 17) * 2 ^ k) := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
end PaddedDescent
