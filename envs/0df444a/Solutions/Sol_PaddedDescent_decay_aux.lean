-- Prove2me | solution 1 for PaddedDescent.decay_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:16:36.856195+00:00
-- url     : https://prove2.me/submissions/c0122b9c-0ad5-41e1-b1f5-655c38ec45f8

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
import Theorems.Thm_PaddedDescent_decay_aux_step

set_option autoImplicit false
section
section
set_option exponentiation.threshold 1024
open PaddedDescent
open WidthK (theta bsum leafC)
open WidthK.Thresholds
namespace PaddedDescent
theorem _root_.solution : ∀ s : ℕ,
    8963 ^ (19 * s / 3 + 700) * (2 ^ 10 * (s + 2 ^ 15) ^ 6 * 2 ^ s) ≤ 10000 ^ (19 * s / 3 + 700)
  | 0 => by norm_num
  | 1 => by norm_num
  | 2 => by norm_num
  | s + 3 => decay_aux_step (solution s)
end PaddedDescent
