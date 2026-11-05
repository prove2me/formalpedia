-- Prove2me | solution 1 for PaddedDescent.tauOf_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:42:48.725823+00:00
-- url     : https://prove2.me/submissions/4d6b6550-30d6-4970-b9d7-7b152c261279

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
theorem _root_.solution (s e : ℕ) : tauOf s ^ e = 2 ^ ((4 * s + 17) * e) := by rw [tauOf, ← pow_mul]
end PaddedDescent
