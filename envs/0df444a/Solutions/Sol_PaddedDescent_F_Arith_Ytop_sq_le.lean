-- Prove2me | solution 1 for PaddedDescent.F.Arith.Ytop_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:15:16.135181+00:00
-- url     : https://prove2.me/submissions/6004d7fd-c6bd-4bf4-b1e4-9616fd753108

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithGlob
import Definitions.Def_PaddedDescent_F_ArithTop
import Definitions.Def_PaddedDescent_F_ArithWalk
import Definitions.Def_PaddedDescent_F_ArithTopInv
import Theorems.Thm_PaddedDescent_F_Arith_one_le_Ytop

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
namespace PaddedDescent.F.Arith
theorem _root_.solution {s n : ℕ} (hY : Ytop s ^ 6 ≤ n) : Ytop s ^ 2 ≤ n :=
  le_trans (Nat.pow_le_pow_right (one_le_Ytop s) (by norm_num)) hY
end PaddedDescent.F.Arith
