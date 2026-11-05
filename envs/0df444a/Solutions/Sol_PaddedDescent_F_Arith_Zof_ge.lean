-- Prove2me | solution 1 for PaddedDescent.F.Arith.Zof_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:03:17.208334+00:00
-- url     : https://prove2.me/submissions/0c6b30c7-5c20-41ca-b49e-3073610bb263

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithGlob
import Definitions.Def_PaddedDescent_F_ArithTop
import Definitions.Def_PaddedDescent_F_ArithWalk
import Definitions.Def_PaddedDescent_F_ArithTopInv
import Theorems.Thm_PaddedDescent_F_Arith_hundred_Ktop_sq_le

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
namespace PaddedDescent.F.Arith
theorem _root_.solution (s : ℕ) : 25 * Kseq (depthOf s) ^ 2 ≤ 2 * Zof s := by
  have h : 100 * Kseq (depthOf s) ^ 2 ≤ Ytop s := hundred_Ktop_sq_le s
  have h2 : Ytop s ≤ Ytop s ^ 2 := Nat.le_self_pow (by norm_num) _
  unfold Zof
  omega
end PaddedDescent.F.Arith
