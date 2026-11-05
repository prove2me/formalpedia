-- Prove2me | solution 1 for PaddedDescent.F.Arith.top_st
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:28:13.924039+00:00
-- url     : https://prove2.me/submissions/fae0d306-2334-4f39-96ab-d0efcfd8117c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithGlob
import Definitions.Def_PaddedDescent_F_ArithTop
import Definitions.Def_PaddedDescent_F_ArithWalk
import Definitions.Def_PaddedDescent_F_ArithTopInv
import Theorems.Thm_PaddedDescent_F_Arith_one_le_Ktop
import Theorems.Thm_PaddedDescent_F_Arith_four_mul_Pbof_le
import Theorems.Thm_PaddedDescent_F_Arith_two_pow_le_of_le
import Theorems.Thm_PaddedDescent_F_Arith_mul_div_le


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
variable {k Δ s n F : ℕ}
namespace PaddedDescent.F.Arith
theorem _root_.solution (hΔ : Δ ≤ 2 ^ betaOf s) (hY : Ytop s ^ 6 ≤ n) (hF : 2 ^ (8 * Xof s n) ≤ F) :
    2 ^ (Pbof Δ s n * (2 * (3 * Kseq (depthOf s) ^ 8) / Kseq (depthOf s))) ≤ F := by
  have h1 : Pbof Δ s n * (2 * gtop s / Ktop s) ≤ Xof s n := mul_div_le (one_le_Ktop s) (four_mul_Pbof_le hΔ hY)
  exact two_pow_le_of_le hF (le_trans h1 (by omega))
end PaddedDescent.F.Arith
