-- Prove2me | solution 1 for PaddedDescent.add_seven_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:08:42.898477+00:00
-- url     : https://prove2.me/submissions/493665c0-37ad-466a-a42c-30d6d3e10ee3

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
theorem _root_.solution (s : ℕ) : s + 7 ≤ 7 * 2 ^ s := by
  have h : s + 1 ≤ 2 ^ s := Nat.lt_two_pow_self
  omega
end PaddedDescent
