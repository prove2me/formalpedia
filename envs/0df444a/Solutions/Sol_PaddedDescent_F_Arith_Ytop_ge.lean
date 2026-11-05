-- Prove2me | solution 1 for PaddedDescent.F.Arith.Ytop_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:09:18.313014+00:00
-- url     : https://prove2.me/submissions/7901fc3d-7da6-41b3-89ef-2e261df90aad

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithGlob
import Definitions.Def_PaddedDescent_F_ArithTop
import Definitions.Def_PaddedDescent_F_ArithWalk
import Definitions.Def_PaddedDescent_F_ArithTopInv
import Theorems.Thm_PaddedDescent_F_Arith_one_le_Ktop
import Theorems.Thm_PaddedDescent_F_Arith_hundred_Ktop_sq_le

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
namespace PaddedDescent.F.Arith
theorem _root_.solution (s : ℕ) : 100 ≤ Ytop s := by
  have h := hundred_Ktop_sq_le s
  have h1 : 1 ≤ Ktop s ^ 2 := Nat.one_le_pow _ _ (one_le_Ktop s)
  omega
end PaddedDescent.F.Arith
