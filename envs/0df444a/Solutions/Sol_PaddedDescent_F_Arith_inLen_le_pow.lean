-- Prove2me | solution 1 for PaddedDescent.F.Arith.inLen_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:01:18.25547+00:00
-- url     : https://prove2.me/submissions/f34e3907-a2e3-4fb6-a832-85ba5f566c80

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_PaddedDescent_Threshold
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_PaddedDescent_F_ArithStack

set_option autoImplicit false
section
section
set_option exponentiation.threshold 1024
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open Groundwork Groundwork.Sparsify PaddedDescent.F.Lists
open WidthK (theta bsum)
open WidthK.Prog (stepK)
namespace PaddedDescent.F.Arith
theorem _root_.solution {k n a : ℕ} (hn : n < a) (hk : 2 ^ (k + 1) ≤ a) : inLen k n ≤ a ^ (k + 4) := by
  have hk1 : k + 1 < 2 ^ (k + 1) := Nat.lt_two_pow_self
  have hk2 : 2 ^ k ≤ a := le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hk
  have h1 : k * 2 ^ k + 1 ≤ a ^ 2 := by
    calc k * 2 ^ k + 1 ≤ k * a + a := Nat.add_le_add (Nat.mul_le_mul_left _ hk2) (by omega)
      _ = (k + 1) * a := by ring
      _ ≤ a * a := Nat.mul_le_mul_right _ (by omega)
      _ = a ^ 2 := by ring
  have h2 : (n + 2) ^ (k + 1) ≤ a ^ (k + 2) := by
    calc (n + 2) ^ (k + 1) ≤ (2 * a) ^ (k + 1) := Nat.pow_le_pow_left (by omega) _
      _ = 2 ^ (k + 1) * a ^ (k + 1) := mul_pow _ _ _
      _ ≤ a * a ^ (k + 1) := Nat.mul_le_mul_right _ hk
      _ = a ^ (k + 2) := by ring
  calc inLen k n = (k * 2 ^ k + 1) * (n + 2) ^ (k + 1) := rfl
    _ ≤ a ^ 2 * a ^ (k + 2) := Nat.mul_le_mul h1 h2
    _ = a ^ (k + 4) := by ring
end PaddedDescent.F.Arith
