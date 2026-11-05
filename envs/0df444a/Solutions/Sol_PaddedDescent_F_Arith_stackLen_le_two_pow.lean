-- Prove2me | solution 1 for PaddedDescent.F.Arith.stackLen_le_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:07:32.857231+00:00
-- url     : https://prove2.me/submissions/5f1548a5-5113-4a6a-81e7-87f2e699c4ca

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_PaddedDescent_Threshold
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_PaddedDescent_F_ArithStack
import Theorems.Thm_PaddedDescent_F_Arith_clause_word_le
import Theorems.Thm_PaddedDescent_F_Arith_inLen_le_pow

set_option autoImplicit false
section
section
set_option exponentiation.threshold 1024
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open Groundwork Groundwork.Sparsify PaddedDescent.F.Lists
open WidthK (theta bsum)
open WidthK.Prog (stepK)
namespace PaddedDescent.F.Arith
theorem _root_.solution {k z n τ : ℕ} (hn : n < 2 ^ z) (hB : bsum τ k ≤ 2 ^ z) (hk : 2 ^ (k + 1) ≤ 2 ^ z) (h8 : 16 ≤ 2 ^ z) :
    stackLen k τ n (inLen k n) ≤ 2 ^ ((k + 12) * z) := by
  obtain ⟨a, ha⟩ : ∃ a, a = 2 ^ z := ⟨_, rfl⟩
  rw [← ha] at hn hB hk h8
  have hk1 : k + 1 < 2 ^ (k + 1) := Nat.lt_two_pow_self
  have hk2 : 2 ^ k ≤ a := le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hk
  have h1 : bsum τ k * n + 1 ≤ a ^ 2 := by
    calc bsum τ k * n + 1 ≤ a * n + a := Nat.add_le_add (Nat.mul_le_mul_right _ hB) (by omega)
      _ = a * (n + 1) := by ring
      _ ≤ a * a := Nat.mul_le_mul_left _ hn
      _ = a ^ 2 := by ring
  have h2 := inLen_le_pow hn hk
  have h3 := clause_word_le hn (show k < a by omega) (show 4 ≤ a by omega)
  have hp8 : 1 ≤ a ^ (k + 8) := Nat.one_le_pow _ _ (by omega)
  have hp11 : 1 ≤ a ^ (k + 11) := Nat.one_le_pow _ _ (by omega)
  have h4 : 2 ^ k * inLen k n * (k * (3 * n + 5) + 10) + 4 ≤ a ^ (k + 9) := by
    calc 2 ^ k * inLen k n * (k * (3 * n + 5) + 10) + 4 ≤ a * a ^ (k + 4) * a ^ 3 + 4 :=
          Nat.add_le_add_right (Nat.mul_le_mul (Nat.mul_le_mul hk2 h2) h3) 4
      _ = a ^ (k + 8) + 4 := by ring
      _ ≤ 8 * a ^ (k + 8) := by omega
      _ ≤ a * a ^ (k + 8) := Nat.mul_le_mul_right _ (by omega)
      _ = a ^ (k + 9) := by ring
  unfold stackLen
  calc (bsum τ k * n + 1) * (2 ^ k * inLen k n * (k * (3 * n + 5) + 10) + 4) + 8 ≤ a ^ 2 * a ^ (k + 9) + 8 :=
        Nat.add_le_add_right (Nat.mul_le_mul h1 h4) 8
    _ = a ^ (k + 11) + 8 := by ring
    _ ≤ 9 * a ^ (k + 11) := by omega
    _ ≤ a * a ^ (k + 11) := Nat.mul_le_mul_right _ (by omega)
    _ = a ^ (k + 12) := by ring
    _ = 2 ^ ((k + 12) * z) := by rw [ha, ← pow_mul, mul_comm]
end PaddedDescent.F.Arith
