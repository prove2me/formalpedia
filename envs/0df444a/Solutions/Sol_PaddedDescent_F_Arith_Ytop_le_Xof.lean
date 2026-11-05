-- Prove2me | solution 1 for PaddedDescent.F.Arith.Ytop_le_Xof
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:16:27.079208+00:00
-- url     : https://prove2.me/submissions/cc23adf4-5f80-434f-b552-e5bfbbd73d51

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithGlob
import Definitions.Def_PaddedDescent_F_ArithTop
import Definitions.Def_PaddedDescent_F_ArithWalk
import Definitions.Def_PaddedDescent_F_ArithTopInv
import Theorems.Thm_PaddedDescent_F_Arith_Ytop_ge
import Theorems.Thm_PaddedDescent_F_Arith_small

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
namespace PaddedDescent.F.Arith
theorem _root_.solution {s n : ℕ} (hY : Ytop s ^ 6 ≤ n) : 65 * Ytop s ≤ Xof s n := by
  have h := small hY
  have h2 : 65 * Ytop s ≤ Ytop s * Ytop s := Nat.mul_le_mul_right _ (le_trans (by norm_num) (Ytop_ge s))
  have e : Ytop s * Ytop s = Ytop s ^ 2 := by ring
  unfold Zof at h
  unfold Xof
  omega
end PaddedDescent.F.Arith
