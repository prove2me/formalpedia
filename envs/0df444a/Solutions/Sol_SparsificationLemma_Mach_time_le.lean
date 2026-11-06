-- Prove2me | solution 1 for SparsificationLemma.Mach.time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:44:02.692801+00:00
-- url     : https://prove2.me/submissions/3eb5f8b5-1a2d-48fb-a77b-1742a9846609

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Mach_Defs
import Definitions.Def_SparsificationLemma_Mach_Cert
import Definitions.Def_SparsificationLemma_Mach_Len
import Definitions.Def_CountKSatRate_Pad
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Definitions.Def_SparsificationLemma_Mach_Main
import Theorems.Thm_SparsificationLemma_Mach_two_pow_size_le
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Mach
open Groundwork CountKSatRate UniformInK PaddedDescent SparsificationLemma.Geo Turing
namespace SparsificationLemma.Mach
theorem _root_.solution (q a k : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    q * (N + 2 ^ (a + k + 3 * Nat.size N + 9) + 1) ^ q ≤ (q * 4097 ^ q + 4 * q) * (N + 2 ^ k) ^ (q * 4097 ^ q + 4 * q) * 2 ^ ((q * 4097 ^ q + 4 * q) * a) := by
  obtain ⟨Y, hY⟩ : ∃ Y, Y = N + 2 ^ k := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = 2 ^ a := ⟨_, rfl⟩
  have hK1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hA1 : 1 ≤ A := hA ▸ Nat.one_le_two_pow
  have hY1 : 1 ≤ Y := by omega
  have hZ : 2 ^ Nat.size N ≤ 2 * Y := (two_pow_size_le hN).trans (by omega)
  have e0 : 2 ^ (a + k + 3 * Nat.size N + 9) = A * 2 ^ k * (2 ^ Nat.size N) ^ 3 * 512 := by
    rw [pow_add, pow_add, pow_add, Nat.mul_comm 3, pow_mul, ← hA]
    norm_num
  have h1 : A * 2 ^ k * (2 ^ Nat.size N) ^ 3 * 512 ≤ A * Y * (2 * Y) ^ 3 * 512 := by gcongr; omega
  have e1 : A * Y * (2 * Y) ^ 3 * 512 = 4096 * (Y ^ 4 * A) := by ring
  have h2 : Y ≤ Y ^ 4 * A := (Nat.le_self_pow (by norm_num) Y).trans (Nat.le_mul_of_pos_right _ hA1)
  have h3 : N + 2 ^ (a + k + 3 * Nat.size N + 9) + 1 ≤ 4097 * (Y ^ 4 * A) := by omega
  have e2 : (4097 * (Y ^ 4 * A)) ^ q = 4097 ^ q * Y ^ (4 * q) * 2 ^ (q * a) := by
    rw [mul_pow, mul_pow, ← pow_mul, hA, ← pow_mul, Nat.mul_comm a q, Nat.mul_assoc]
  rw [← hY]
  calc q * (N + 2 ^ (a + k + 3 * Nat.size N + 9) + 1) ^ q ≤ q * (4097 * (Y ^ 4 * A)) ^ q := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h3 q)
    _ = q * 4097 ^ q * Y ^ (4 * q) * 2 ^ (q * a) := by rw [e2]; ring
    _ ≤ _ := by
      refine Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.pow_le_pow_right hY1 (Nat.le_add_left _ _))) (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ ?_))
      exact (Nat.le_mul_of_pos_right q (Nat.pow_pos (by norm_num))).trans (Nat.le_add_right _ _)
end SparsificationLemma.Mach
