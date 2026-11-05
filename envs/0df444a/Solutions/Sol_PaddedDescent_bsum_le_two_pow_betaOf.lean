-- Prove2me | solution 1 for PaddedDescent.bsum_le_two_pow_betaOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:54:11.890831+00:00
-- url     : https://prove2.me/submissions/7990eb17-a1c1-44d3-9e27-bf65d97a271b

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
import Theorems.Thm_PaddedDescent_two_le_tauOf
import Theorems.Thm_PaddedDescent_three_mul_tauOf_mul_bsum_le

set_option autoImplicit false
section
section
set_option exponentiation.threshold 1024
open PaddedDescent
open WidthK (theta bsum leafC)
open WidthK.Thresholds
namespace PaddedDescent
theorem _root_.solution {k s : ℕ} (hs : s0K k ≤ s) : bsum (tauOf s) k ≤ 2 ^ betaOf s := by
  have h1 : 1 ≤ 3 * tauOf s := by have := two_le_tauOf s; omega
  exact le_trans (Nat.le_mul_of_pos_left _ h1) (three_mul_tauOf_mul_bsum_le hs)
end PaddedDescent
