-- Prove2me | solution 1 for UniformInK.Leaves.sq_le_of_s0U_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:57:54.506103+00:00
-- url     : https://prove2.me/submissions/fa3c6b5d-3d29-4858-b447-89d3a425d36d

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

set_option autoImplicit false
section
open UniformInK UniformInK.Leaves
open PaddedDescent
namespace UniformInK.Leaves
theorem _root_.solution {k s : ℕ} (hs : s0U k ≤ s) : k ^ 2 ≤ 2 ^ s := by
  have h1 : k ≤ 2 ^ Nat.size k := (Nat.lt_size_self k).le
  calc k ^ 2 ≤ (2 ^ Nat.size k) ^ 2 := Nat.pow_le_pow_left h1 2
    _ = 2 ^ s0U k := by rw [← pow_mul, s0U, Nat.mul_comm]
    _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
end UniformInK.Leaves
