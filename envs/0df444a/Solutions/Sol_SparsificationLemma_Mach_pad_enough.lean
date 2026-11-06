-- Prove2me | solution 1 for SparsificationLemma.Mach.pad_enough
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:34:55.735941+00:00
-- url     : https://prove2.me/submissions/2738f019-de74-4c20-9f4a-8deab1ee16e1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Mach_Walk
import Definitions.Def_SparsificationLemma_Side
import Definitions.Def_UniformInK_Tree_Tree
import Definitions.Def_UniformInK_Spars_Main
import Definitions.Def_UniformInK_Top_Leaves
import Definitions.Def_UniformInK_Top_Budget
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_CountKSatRate_Leaf
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Definitions.Def_SparsificationLemma_Mach_Len
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Mach
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSatRate UniformInK PaddedDescent PaddedDescent.F ClauseBound.Alg SparsificationLemma.Geo
namespace SparsificationLemma.Mach
theorem _root_.solution (a : ℕ) {k n m N : ℕ} (hk : k ≤ N) (hn : n ≤ N) (hm : m ≤ N) :
    2 ^ (a + 1) * (nodeLen k n m + 2) + 6 ≤ 2 ^ (a + k + 3 * Nat.size N + 9) := by
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = 2 ^ Nat.size N := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = 2 ^ k := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = 2 ^ a := ⟨_, rfl⟩
  have hNZ : N < Z := hZ ▸ Nat.lt_size_self N
  have hK1 : 1 ≤ K := hK ▸ Nat.one_le_two_pow
  have hA1 : 1 ≤ A := hA ▸ Nat.one_le_two_pow
  have hZ1 : 1 ≤ Z := by omega
  have e0 : 2 ^ (a + k + 3 * Nat.size N + 9) = A * K * Z ^ 3 * 512 := by
    rw [pow_add, pow_add, pow_add, Nat.mul_comm 3, pow_mul, ← hZ, ← hK, ← hA]
    norm_num
  have e1 : 2 ^ (a + 1) = 2 * A := by rw [pow_succ, ← hA, Nat.mul_comm]
  have b1 : Z ≤ Z ^ 3 := Nat.le_self_pow (by norm_num) Z
  have b2 : Z ^ 2 ≤ Z ^ 3 := Nat.pow_le_pow_right hZ1 (by norm_num)
  have b3 : 1 ≤ Z ^ 3 := Nat.one_le_pow _ _ hZ1
  have c1 : m * (k * (3 * n + 5) + 10) ≤ Z * (Z * (3 * Z + 5) + 10) := by gcongr <;> omega
  have c2 : 2 * n * (2 * (3 * n + 5) + 10) ≤ 2 * Z * (2 * (3 * Z + 5) + 10) := by gcongr <;> omega
  have e2 : Z * (Z * (3 * Z + 5) + 10) = 3 * Z ^ 3 + 5 * Z ^ 2 + 10 * Z := by ring
  have e3 : 2 * Z * (2 * (3 * Z + 5) + 10) = 12 * Z ^ 2 + 40 * Z := by ring
  have c3 : K * (m * (k * (3 * n + 5) + 10)) ≤ K * (18 * Z ^ 3) := Nat.mul_le_mul_left _ (by omega)
  have c4 : 60 * Z ^ 3 ≤ K * (60 * Z ^ 3) := Nat.le_mul_of_pos_left _ hK1
  have c5 : nodeLen k n m + 2 ≤ K * (78 * Z ^ 3) := by
    have e4 : K * (78 * Z ^ 3) = K * (18 * Z ^ 3) + K * (60 * Z ^ 3) := by ring
    rw [nodeLen, ← hK, Nat.mul_assoc K, e4]
    omega
  have c6 : 1 ≤ A * K * Z ^ 3 := Nat.mul_pos (Nat.mul_pos hA1 hK1) b3
  calc 2 ^ (a + 1) * (nodeLen k n m + 2) + 6 ≤ 2 * A * (K * (78 * Z ^ 3)) + 6 := by rw [e1]; gcongr
    _ = 156 * (A * K * Z ^ 3) + 6 := by ring
    _ ≤ A * K * Z ^ 3 * 512 := by omega
    _ = _ := e0.symm
end SparsificationLemma.Mach
