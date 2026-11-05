-- Prove2me | solution 1 for PaddedDescent.three_mul_tauOf_mul_bsum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:44:11.086977+00:00
-- url     : https://prove2.me/submissions/2b3c6047-96c7-4f3d-b033-2c868a330d73

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
import Theorems.Thm_PaddedDescent_bsum_tauOf_le
import Theorems.Thm_PaddedDescent_exponent_le_betaOf

set_option autoImplicit false
section
section
set_option exponentiation.threshold 1024
open PaddedDescent
open WidthK (theta bsum leafC)
open WidthK.Thresholds
namespace PaddedDescent
theorem _root_.solution {k s : ℕ} (hs : s0K k ≤ s) : 3 * tauOf s * bsum (tauOf s) k ≤ 2 ^ betaOf s := by
  have h := exponent_le_betaOf hs
  calc 3 * tauOf s * bsum (tauOf s) k ≤ 2 ^ 2 * 2 ^ (4 * s + 17) * 2 ^ ((4 * s + 17) * 2 ^ (k + 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) le_rfl) (bsum_tauOf_le k s)
    _ = 2 ^ (2 + (4 * s + 17) + (4 * s + 17) * 2 ^ (k + 1)) := by rw [← pow_add, ← pow_add]
    _ ≤ 2 ^ betaOf s := Nat.pow_le_pow_right (by norm_num) (by
        have e : (4 * s + 17) * (2 ^ (k + 1) + 1) = (4 * s + 17) * 2 ^ (k + 1) + (4 * s + 17) := by ring
        omega)
end PaddedDescent
