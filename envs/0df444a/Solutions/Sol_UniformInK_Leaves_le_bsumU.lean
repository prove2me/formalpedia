-- Prove2me | solution 1 for UniformInK.Leaves.le_bsumU
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:20:59.894663+00:00
-- url     : https://prove2.me/submissions/3cad22d8-8c66-4f88-8818-14b56bed5bb3

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
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
open UniformInK UniformInK.Leaves
open PaddedDescent
namespace UniformInK.Leaves
theorem _root_.solution (k s : ℕ) : k ≤ bsumU (tauOf s) k := by
  rw [bsumU_tauOf]
  refine Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by norm_num) ?_)
  unfold betaU
  nlinarith
end UniformInK.Leaves
