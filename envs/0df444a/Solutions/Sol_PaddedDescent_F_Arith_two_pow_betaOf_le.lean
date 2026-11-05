-- Prove2me | solution 1 for PaddedDescent.F.Arith.two_pow_betaOf_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:04:27.422741+00:00
-- url     : https://prove2.me/submissions/a32a06f9-3aa8-46af-9e8f-ce78d0d3aaa7

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
import Theorems.Thm_PaddedDescent_Ytop_sOf_pow_le
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
theorem _root_.solution {n : ℕ} (hs : 1 ≤ sOf n) : 2 ^ (4 * betaOf (sOf n) + 10 * sOf n + 1000) ≤ n := by
  have h3 := Ytop_sOf_pow_le (p := 1) (by norm_num) hs
  rw [pow_one] at h3
  exact ((two_pow_betaOf_le_Ktop _).trans (Ktop_le_Ytop _)).trans h3
end PaddedDescent.F.Arith
