-- Prove2me | solution 1 for PaddedDescent.F.Arith.betaOf_lt_Ytop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:04:21.648378+00:00
-- url     : https://prove2.me/submissions/fbf1b673-590e-4cf0-a502-b326b77bb00f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_PaddedDescent_Threshold
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_PaddedDescent_F_ArithStack
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_PaddedDescent_Ktop_le_Ytop
import Theorems.Thm_PaddedDescent_two_pow_betaOf_le_Ktop


set_option autoImplicit false
section
section
set_option exponentiation.threshold 1024
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open Groundwork Groundwork.Sparsify PaddedDescent.F.Lists
open WidthK (theta bsum)
open WidthK.Prog (stepK)
namespace PaddedDescent.F.Arith
theorem _root_.solution (s : ℕ) : 4 * betaOf s + 10 * s + 1000 < Ytop s :=
  lt_of_lt_of_le Nat.lt_two_pow_self ((two_pow_betaOf_le_Ktop s).trans (Ktop_le_Ytop s))
end PaddedDescent.F.Arith
