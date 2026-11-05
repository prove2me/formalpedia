-- Prove2me | solution 1 for UniformInK.Leaves.bsumU_tauOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:46:22.577735+00:00
-- url     : https://prove2.me/submissions/4d660a1e-7c20-4655-8c1c-23bf0fb2f3f0

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
import Theorems.Thm_PaddedDescent_tauOf_pow


set_option autoImplicit false
section
open UniformInK UniformInK.Leaves
open PaddedDescent
namespace UniformInK.Leaves
theorem _root_.solution (k s : ℕ) : bsumU (tauOf s) k = 2 ^ betaU k s := by
  rw [bsumU, tauOf_pow, betaU]
  congr 1
  ring
end UniformInK.Leaves
