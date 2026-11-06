-- Prove2me | solution 1 for UniformInK.Leaves.three_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:39:00.825201+00:00
-- url     : https://prove2.me/submissions/03f920fb-1535-4240-a1b4-1490ac2aaa3e

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
import Theorems.Thm_UniformInK_Leaves_bsumU_tauOf
import Theorems.Thm_Groundwork_PolyT_congr


set_option autoImplicit false
section
open UniformInK UniformInK.Leaves
open PaddedDescent
namespace UniformInK.Leaves
theorem _root_.solution (k s : ℕ) : 3 * tauOf s * bsumU (tauOf s) k ≤ 2 ^ (betaU k s + 4 * s + 19) := by
  rw [bsumU_tauOf, tauOf]
  calc 3 * 2 ^ (4 * s + 17) * 2 ^ betaU k s ≤ 2 ^ 2 * 2 ^ (4 * s + 17) * 2 ^ betaU k s :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))
    _ = 2 ^ (betaU k s + 4 * s + 19) := by rw [← pow_add, ← pow_add]; congr 1; omega
end UniformInK.Leaves
