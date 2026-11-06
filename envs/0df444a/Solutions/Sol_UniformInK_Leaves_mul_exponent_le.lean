-- Prove2me | solution 1 for UniformInK.Leaves.mul_exponent_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:39:05.773915+00:00
-- url     : https://prove2.me/submissions/059b0b66-ae01-46ed-908a-0ee5794abe69

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_PaddedDescent_Choice
import Definitions.Def_SparsifyWidthK_Thresholds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_UniformInK_Top_Leaves
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
open UniformInK UniformInK.Leaves
open PaddedDescent
namespace UniformInK.Leaves
theorem _root_.solution {k s : ℕ} (hk : 1 ≤ k) (hs : k ^ 2 ≤ 2 ^ s) : k * (betaU k s + 4 * s + 19) * 2 ^ s ≤ tauOf s := by
  have h1 : s + 1 ≤ 2 ^ s := Nat.lt_two_pow_self
  have h2 : 4 * s + 17 ≤ 17 * 2 ^ s := by omega
  have h3 : k * (betaU k s + 4 * s + 19) ≤ 4 * k ^ 2 * (4 * s + 17) := by
    unfold betaU
    nlinarith [Nat.mul_le_mul hk hk, Nat.mul_le_mul_right s (Nat.mul_le_mul hk hk), Nat.mul_le_mul_left k hk, Nat.mul_le_mul_right s (Nat.mul_le_mul_left k hk)]
  calc k * (betaU k s + 4 * s + 19) * 2 ^ s ≤ 4 * 2 ^ s * (17 * 2 ^ s) * 2 ^ s :=
        Nat.mul_le_mul_right _ (h3.trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ hs) h2))
    _ = 68 * 2 ^ (3 * s) := by rw [show 3 * s = s + s + s by ring, pow_add, pow_add]; ring
    _ ≤ 2 ^ (s + 17) * 2 ^ (3 * s) := Nat.mul_le_mul_right _ (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left 17 s)))
    _ = tauOf s := by rw [tauOf, ← pow_add]; congr 1; omega
end UniformInK.Leaves
