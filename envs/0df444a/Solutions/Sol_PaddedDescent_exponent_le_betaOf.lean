-- Prove2me | solution 1 for PaddedDescent.exponent_le_betaOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:10:05.670075+00:00
-- url     : https://prove2.me/submissions/d2853756-17db-4475-b6f4-456522bcd28b

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

set_option autoImplicit false
section
section
set_option exponentiation.threshold 1024
open PaddedDescent
open WidthK (theta bsum leafC)
open WidthK.Thresholds
namespace PaddedDescent
theorem _root_.solution {k s : ℕ} (hs : s0K k ≤ s) : (4 * s + 17) * (2 ^ (k + 1) + 1) + k + 3 ≤ betaOf s := by
  have hk : k + 1 < 2 ^ (k + 1) := Nat.lt_two_pow_self
  have e : s0K k = 8 * 2 ^ (k + 1) := by rw [s0K, show k + 4 = k + 1 + 3 by ring, pow_add]; ring
  rw [e] at hs
  unfold betaOf
  generalize 2 ^ (k + 1) = a at hk hs ⊢
  nlinarith [Nat.mul_le_mul hs (le_refl s)]
end PaddedDescent
