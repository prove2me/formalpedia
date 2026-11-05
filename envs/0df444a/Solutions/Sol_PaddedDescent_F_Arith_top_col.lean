-- Prove2me | solution 1 for PaddedDescent.F.Arith.top_col
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:21:08.919203+00:00
-- url     : https://prove2.me/submissions/5c07ad9d-3211-4cca-988a-d5beff8c5a1a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithGlob
import Definitions.Def_PaddedDescent_F_ArithTop
import Definitions.Def_PaddedDescent_F_ArithWalk
import Definitions.Def_PaddedDescent_F_ArithTopInv
import Theorems.Thm_PaddedDescent_F_Arith_Ktop_le_gtop
import Theorems.Thm_PaddedDescent_F_Arith_Ytop_le_Xof
import Theorems.Thm_PaddedDescent_F_Arith_two_pow_le_of_le
import Theorems.Thm_PaddedDescent_F_Arith_pow_le_two_pow_sq
import Theorems.Thm_PaddedDescent_Ytop_eq_sq


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
variable {k Δ s n F : ℕ}
namespace PaddedDescent.F.Arith
theorem _root_.solution (hY : Ytop s ^ 6 ≤ n) (hF : 2 ^ (8 * Xof s n) ≤ F) :
    Kseq (depthOf s) ^ (3 * Kseq (depthOf s) ^ 8) ≤ F := by
  have h1 : Ktop s ^ gtop s ≤ 2 ^ (gtop s * gtop s) := pow_le_two_pow_sq (Ktop_le_gtop s)
  have e : gtop s * gtop s = Ytop s := by rw [Ytop_eq_sq]; ring
  rw [e] at h1
  have h2 := Ytop_le_Xof hY
  exact le_trans h1 (two_pow_le_of_le hF (by omega))
end PaddedDescent.F.Arith
