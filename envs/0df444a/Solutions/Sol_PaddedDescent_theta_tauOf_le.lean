-- Prove2me | solution 1 for PaddedDescent.theta_tauOf_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:54:10.731561+00:00
-- url     : https://prove2.me/submissions/ea940872-7cc3-44fd-8f23-5ed53f9ecf06

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
import Theorems.Thm_PaddedDescent_one_le_tauOf
import Theorems.Thm_PaddedDescent_tauOf_pow
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_WidthK_Thresholds_sq_mul_theta_le


set_option autoImplicit false
section
section
set_option exponentiation.threshold 1024
open PaddedDescent
open WidthK (theta bsum leafC)
open WidthK.Thresholds
namespace PaddedDescent
theorem _root_.solution {j k : ℕ} (hj : j < k) (s : ℕ) : theta (tauOf s) j ≤ 2 ^ ((4 * s + 17) * 2 ^ k) := by
  have h1 := sq_mul_theta_le (four_le_tauOf s) j
  have h2 : theta (tauOf s) j ≤ tauOf s ^ 2 * theta (tauOf s) j :=
    Nat.le_mul_of_pos_left _ (Nat.pow_pos (lt_of_lt_of_le (by norm_num) (one_le_tauOf s)))
  calc theta (tauOf s) j ≤ tauOf s ^ 2 ^ (j + 1) := h2.trans h1
    _ = 2 ^ ((4 * s + 17) * 2 ^ (j + 1)) := tauOf_pow s _
    _ ≤ 2 ^ ((4 * s + 17) * 2 ^ k) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hj))
end PaddedDescent
