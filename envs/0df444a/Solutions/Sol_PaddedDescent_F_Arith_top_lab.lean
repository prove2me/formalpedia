-- Prove2me | solution 1 for PaddedDescent.F.Arith.top_lab
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:28:18.987221+00:00
-- url     : https://prove2.me/submissions/281e263e-1c80-4fe2-a9c4-3fbffeb94728

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithGlob
import Definitions.Def_PaddedDescent_F_ArithTop
import Definitions.Def_PaddedDescent_F_ArithWalk
import Definitions.Def_PaddedDescent_F_ArithTopInv
import Theorems.Thm_PaddedDescent_F_Arith_Ktop_le_gtop
import Theorems.Thm_PaddedDescent_F_Arith_gtop_pos
import Theorems.Thm_PaddedDescent_F_Arith_four_mul_Pbof_le
import Theorems.Thm_PaddedDescent_F_Arith_two_pow_le_of_le
import Theorems.Thm_PaddedDescent_F_Arith_size_le


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
variable {k Δ s n F : ℕ}
namespace PaddedDescent.F.Arith
theorem _root_.solution (hΔ : Δ ≤ 2 ^ betaOf s) (hY : Ytop s ^ 6 ≤ n) (hF : 2 ^ (8 * Xof s n) ≤ F) : 2 ^ Pbof Δ s n ≤ F := by
  have h1 : Pbof Δ s n ≤ Xof s n := size_le (gtop_pos s) (Ktop_le_gtop s) (four_mul_Pbof_le hΔ hY)
  exact two_pow_le_of_le hF (le_trans h1 (by omega))
end PaddedDescent.F.Arith
