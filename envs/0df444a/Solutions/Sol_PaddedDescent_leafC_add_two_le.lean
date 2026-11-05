-- Prove2me | solution 1 for PaddedDescent.leafC_add_two_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:59:28.393782+00:00
-- url     : https://prove2.me/submissions/860fdd1a-c6c0-403d-8f63-af33bb5be037

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
import Theorems.Thm_PaddedDescent_leafC_tauOf_le
import Theorems.Thm_PaddedDescent_exponent_le_betaOf

set_option autoImplicit false
section
section
set_option exponentiation.threshold 1024
open PaddedDescent
open WidthK (theta bsum leafC)
open WidthK.Thresholds
namespace PaddedDescent
theorem _root_.solution {k s : ℕ} (hs : s0K k ≤ s) : leafC (tauOf s) k + 2 ≤ 2 ^ betaOf s := by
  have h := exponent_le_betaOf hs
  have hk : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  obtain ⟨E, hE⟩ : ∃ E, E = (4 * s + 17) * 2 ^ k := ⟨_, rfl⟩
  have hE1 : 1 ≤ 2 ^ E := Nat.one_le_two_pow
  have h2 : E + k + 1 ≤ betaOf s := by
    have e1 : (4 * s + 17) * (2 ^ (k + 1) + 1) = 2 * E + (4 * s + 17) := by rw [hE, pow_succ]; ring
    omega
  calc leafC (tauOf s) k + 2 ≤ 2 * (k * 2 ^ E) + 2 * 2 ^ E := Nat.add_le_add (hE ▸ leafC_tauOf_le k s) (by omega)
    _ = 2 * ((k + 1) * 2 ^ E) := by ring
    _ ≤ 2 * (2 ^ k * 2 ^ E) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hk)
    _ = 2 ^ (E + k + 1) := by rw [pow_add, pow_add]; ring
    _ ≤ 2 ^ betaOf s := Nat.pow_le_pow_right (by norm_num) h2
end PaddedDescent
