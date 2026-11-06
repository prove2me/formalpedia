-- Prove2me | solution 1 for UniformInK.Budget.stack_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:39:14.076873+00:00
-- url     : https://prove2.me/submissions/77d6d53e-5bf4-44ec-b079-ae460918897f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_UniformInK_Top_Leaves
import Definitions.Def_ClauseBound_ParityChecks_BudgetOL
import Definitions.Def_ClauseBound_ParityChecks_BudgetOL
import Definitions.Def_PaddedDescent_Choice
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_UniformInK_Top_Budget
import Theorems.Thm_ClauseBound_ParityChecks_BudgetOL_add_le_pow
import Theorems.Thm_ClauseBound_ParityChecks_BudgetOL_clause_le
import Theorems.Thm_ClauseBound_ParityChecks_BudgetOL_inLen_le
import Theorems.Thm_ClauseBound_ParityChecks_BudgetOL_mul_le_pow
import Theorems.Thm_ClauseBound_ParityChecks_BudgetOL_succ_le_size
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_UniformInK_Leaves_bsumU_tauOf
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open UniformInK UniformInK.Budget
open PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.TopN ClauseBound.ParityChecks ClauseBound.ParityChecks.BudgetOL UniformInK.Leaves
namespace UniformInK.Budget
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) (n s : ℕ) : stackLenCU k (tauOf s) n (inLen k n) ≤ 2 ^ (betaU k s + 5 * k + 10 + (k + 3) * Nat.size n) := by
  obtain ⟨β, hβ⟩ : ∃ β, β = betaU k s := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, z = Nat.size n := ⟨_, rfl⟩
  obtain ⟨kz, hkz⟩ : ∃ kz, kz = k * z := ⟨_, rfl⟩
  have hn1 : n + 1 ≤ 2 ^ z := hz ▸ succ_le_size n
  have hcl : k * (3 * n + 5) + 10 ≤ 2 ^ (k + z + 4) := hz ▸ clause_le k n
  have hB1 : 1 ≤ 2 ^ β := Nat.one_le_two_pow
  have he : betaU k s + 5 * k + 10 + (k + 3) * Nat.size n = β + 5 * k + 10 + (kz + 3 * z) := by
    rw [← hβ, ← hz, hkz]
    ring
  rw [he]
  unfold stackLenCU
  rw [bsumU_tauOf, ← hβ]
  have b1 : 2 ^ β * n + 1 ≤ 2 ^ (β + z) := by
    calc 2 ^ β * n + 1 ≤ 2 ^ β * (n + 1) := by nlinarith
      _ ≤ 2 ^ β * 2 ^ z := Nat.mul_le_mul_left _ hn1
      _ = 2 ^ (β + z) := (pow_add _ _ _).symm
  have hin : inLen k n ≤ 2 ^ (3 * k + 1 + (kz + z)) := by
    have h := inLen_le k n
    rw [← hz, show (k + 1) * z = k * z + z by ring, ← hkz] at h
    exact h
  have b2 : 2 ^ k * inLen k n * (k * (3 * n + 5) + 10) ≤ 2 ^ (k + (3 * k + 1 + (kz + z)) + (k + z + 4)) :=
    mul_le_pow (mul_le_pow le_rfl hin) hcl
  have b3 : 2 * n * (2 * (3 * n + 5) + 10) + 8 ≤ 2 ^ (z + z + 6) := by
    have h1 : (n + 1) * (n + 1) ≤ 2 ^ z * 2 ^ z := Nat.mul_le_mul hn1 hn1
    have h2 : 2 * n * (2 * (3 * n + 5) + 10) + 8 ≤ 64 * ((n + 1) * (n + 1)) := by nlinarith
    calc 2 * n * (2 * (3 * n + 5) + 10) + 8 ≤ 64 * (2 ^ z * 2 ^ z) := h2.trans (Nat.mul_le_mul_left _ h1)
      _ = 2 ^ (z + z + 6) := by rw [pow_add, pow_add]; ring
  have b4 : 2 ^ k * inLen k n * (k * (3 * n + 5) + 10) + (2 * n * (2 * (3 * n + 5) + 10) + 8) ≤ 2 ^ (5 * k + 6 + kz + 2 * z) :=
    add_le_pow b2 b3 (by omega) (by omega)
  have b5 : (2 ^ β * n + 1) * (2 ^ k * inLen k n * (k * (3 * n + 5) + 10) + 2 * n * (2 * (3 * n + 5) + 10) + 8) ≤
      2 ^ (β + z + (5 * k + 6 + kz + 2 * z)) := by
    rw [Nat.add_assoc (2 ^ k * inLen k n * (k * (3 * n + 5) + 10))]
    exact mul_le_pow b1 b4
  have b6 : 3 * n + 16 ≤ 2 ^ (z + 4) := by rw [pow_add]; omega
  have b7 := add_le_pow (r := β + 5 * k + 10 + (kz + 3 * z)) b5 b6 (by omega) (by omega)
  rw [Nat.add_assoc]
  exact b7
end UniformInK.Budget
