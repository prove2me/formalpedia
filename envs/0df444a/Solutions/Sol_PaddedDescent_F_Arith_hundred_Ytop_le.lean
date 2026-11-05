-- Prove2me | solution 1 for PaddedDescent.F.Arith.hundred_Ytop_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:20:44.588003+00:00
-- url     : https://prove2.me/submissions/1c94d83b-1e5e-4589-b9ea-d366db77f6f9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithGlob
import Definitions.Def_PaddedDescent_F_ArithTop
import Definitions.Def_PaddedDescent_F_ArithWalk
import Definitions.Def_PaddedDescent_F_ArithTopInv
import Theorems.Thm_PaddedDescent_F_Arith_Ytop_ge
import Theorems.Thm_PaddedDescent_F_Arith_Ytop_sq_le

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
namespace PaddedDescent.F.Arith
theorem _root_.solution {s n : ℕ} (hY : Ytop s ^ 6 ≤ n) : 100 * Ytop s ≤ n := by
  have h1 := Ytop_sq_le hY
  have h2 : 100 * Ytop s ≤ Ytop s * Ytop s := Nat.mul_le_mul_right _ (Ytop_ge s)
  have h3 : Ytop s * Ytop s = Ytop s ^ 2 := by ring
  omega
end PaddedDescent.F.Arith
