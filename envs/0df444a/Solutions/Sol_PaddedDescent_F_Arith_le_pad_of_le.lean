-- Prove2me | solution 1 for PaddedDescent.F.Arith.le_pad_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:03:04.66646+00:00
-- url     : https://prove2.me/submissions/838cef90-ea3b-4964-8c59-4d7258fc9d92

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_PaddedDescent_Threshold
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_PaddedDescent_F_ArithStack
import Theorems.Thm_PaddedDescent_F_Arith_nine_size_le
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
set_option exponentiation.threshold 1024
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open Groundwork Groundwork.Sparsify PaddedDescent.F.Lists
open WidthK (theta bsum)
open WidthK.Prog (stepK)
namespace PaddedDescent.F.Arith
theorem _root_.solution {n W C₀ F : ℕ} (hs : 1 ≤ sOf n) (hC : 1 ≤ C₀) (hF : 2 ^ (C₀ * (n / 2 ^ sOf n + 1)) ≤ F)
    (hW : W ≤ 2 ^ (9 * Nat.size n + 30)) : W ≤ F := by
  refine hW.trans (le_trans (Nat.pow_le_pow_right (by norm_num) ?_) hF)
  have := nine_size_le hs
  nlinarith
end PaddedDescent.F.Arith
