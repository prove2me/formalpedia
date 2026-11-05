-- Prove2me | solution 1 for PaddedDescent.F.Arith.mul_size_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:56:31.202285+00:00
-- url     : https://prove2.me/submissions/d2815b42-e738-4dea-8e55-eff2c8781fcf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_PaddedDescent_Threshold
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_PaddedDescent_F_ArithStack
import Theorems.Thm_PaddedDescent_overhead_sOf_le_div
import Theorems.Thm_PaddedDescent_size_le_sqrt


set_option autoImplicit false
section
section
set_option exponentiation.threshold 1024
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open Groundwork Groundwork.Sparsify PaddedDescent.F.Lists
open WidthK (theta bsum)
open WidthK.Prog (stepK)
namespace PaddedDescent.F.Arith
theorem _root_.solution {n e : ℕ} (hs : 1 ≤ sOf n) (he : e ≤ Ytop (sOf n)) : e * Nat.size n ≤ n / 2 ^ sOf n := by
  refine overhead_sOf_le_div (a := 1) (c := 2) hs (by norm_num) (by norm_num) ?_
  have h := size_le_sqrt n
  calc e * Nat.size n ≤ Ytop (sOf n) * (2 * Nat.sqrt n + 2) := Nat.mul_le_mul he h
    _ = 2 * Ytop (sOf n) ^ 1 * (Nat.sqrt n + 1) := by ring
end PaddedDescent.F.Arith
