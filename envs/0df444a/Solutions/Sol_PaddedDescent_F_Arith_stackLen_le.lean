-- Prove2me | solution 1 for PaddedDescent.F.Arith.stackLen_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:12:40.632122+00:00
-- url     : https://prove2.me/submissions/ae16a1d1-f744-4783-9fd8-74fe08117f95

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_PaddedDescent_Threshold
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_PaddedDescent_F_ArithStack
import Theorems.Thm_PaddedDescent_F_Arith_le_pad_of_le_pow
import Theorems.Thm_PaddedDescent_F_Arith_betaOf_lt_Ytop
import Theorems.Thm_PaddedDescent_F_Arith_two_pow_betaOf_le
import Theorems.Thm_PaddedDescent_F_Arith_stackLen_le_two_pow
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_PaddedDescent_bsum_le_two_pow_betaOf
import Theorems.Thm_PaddedDescent_le_of_s0K_le


set_option autoImplicit false
section
section
set_option exponentiation.threshold 1024
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open Groundwork Groundwork.Sparsify PaddedDescent.F.Lists
open WidthK (theta bsum)
open WidthK.Prog (stepK)
namespace PaddedDescent.F.Arith
theorem _root_.solution {k n C₀ F : ℕ} (hk : 1 ≤ k) (hs : s0K k ≤ sOf n) (hC : 1 ≤ C₀) (hF : 2 ^ (C₀ * (n / 2 ^ sOf n + 1)) ≤ F) :
    stackLen k (tauOf (sOf n)) n (inLen k n) ≤ F := by
  have hks := le_of_s0K_le hs
  have hs1 : 1 ≤ sOf n := hk.trans hks
  have hn := Nat.lt_size_self n
  have hbig := two_pow_betaOf_le hs1
  have hY := betaOf_lt_Ytop (sOf n)
  refine le_pad_of_le_pow hs1 hC hF (e := k + 12) (by omega) (stackLen_le_two_pow hn ?_ ?_ ?_)
  · exact ((bsum_le_two_pow_betaOf hs).trans (Nat.pow_le_pow_right (by norm_num) (by omega))).trans (hbig.trans hn.le)
  · exact (Nat.pow_le_pow_right (by norm_num) (by omega)).trans (hbig.trans hn.le)
  · exact (show 16 ≤ 2 ^ 4 by norm_num).trans ((Nat.pow_le_pow_right (by norm_num) (by omega)).trans (hbig.trans hn.le))
end PaddedDescent.F.Arith
