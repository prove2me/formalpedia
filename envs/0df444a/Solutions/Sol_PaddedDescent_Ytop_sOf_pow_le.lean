-- Prove2me | solution 1 for PaddedDescent.Ytop_sOf_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:37:44.994991+00:00
-- url     : https://prove2.me/submissions/201044cd-4c4b-494c-89ac-c95a453086ad

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Choice
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_PaddedDescent_Threshold
import Theorems.Thm_PaddedDescent_Ytop_pow_le
import Theorems.Thm_PaddedDescent_two_pow_two_pow_sOf_le
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open PaddedDescent
namespace PaddedDescent
theorem _root_.solution {n p : ℕ} (hp : p ≤ 2 ^ 200) (h : 1 ≤ sOf n) : Ytop (sOf n) ^ p ≤ n :=
  (Ytop_pow_le hp (sOf n)).trans (two_pow_two_pow_sOf_le h)
end PaddedDescent
