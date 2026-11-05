-- Prove2me | solution 1 for PaddedDescent.bsum_tauOf_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:41:02.716478+00:00
-- url     : https://prove2.me/submissions/95e6d91d-6277-40f8-90e4-687fa3970d72

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
import Theorems.Thm_PaddedDescent_four_le_tauOf
import Theorems.Thm_PaddedDescent_tauOf_pow
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_WidthK_Thresholds_bsum_le_pow


set_option autoImplicit false
section
section
set_option exponentiation.threshold 1024
open PaddedDescent
open WidthK (theta bsum leafC)
open WidthK.Thresholds
namespace PaddedDescent
theorem _root_.solution (k s : ℕ) : bsum (tauOf s) k ≤ 2 ^ ((4 * s + 17) * 2 ^ (k + 1)) :=
  (bsum_le_pow (four_le_tauOf s) k).trans (tauOf_pow s _).le
end PaddedDescent
