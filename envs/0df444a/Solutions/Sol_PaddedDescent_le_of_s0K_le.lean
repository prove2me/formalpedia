-- Prove2me | solution 1 for PaddedDescent.le_of_s0K_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:40:26.19997+00:00
-- url     : https://prove2.me/submissions/ff6ce510-aeb9-40c5-b559-7077894ac4f4

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
theorem _root_.solution {k s : ℕ} (hs : s0K k ≤ s) : k ≤ s := by
  have h1 : k < 2 ^ k := Nat.lt_two_pow_self
  have h2 : 2 ^ k ≤ 2 ^ (k + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold s0K at hs
  omega
end PaddedDescent
