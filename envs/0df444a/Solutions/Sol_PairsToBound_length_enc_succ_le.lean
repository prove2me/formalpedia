-- Prove2me | solution 1 for PairsToBound.length_enc_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:13:58.791707+00:00
-- url     : https://prove2.me/submissions/10157472-3ccf-4f95-b94a-50f22b184df9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Width
import Definitions.Def_VariableBound_Paper_Forms
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSat_Poly
import Definitions.Def_CountKSatRate_Brute
import Definitions.Def_CountKSatRate_Cert
import Definitions.Def_CountKSatRate_Pad
import Definitions.Def_Wrap_Sim
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Lib_List1b
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_PairsToBound_Exhaust
import Theorems.Thm_PairsToBound_clauseCountPow_of_two_le
import Theorems.Thm_ClauseBound_Alg_End_length_enc
import Theorems.Thm_Groundwork_DecodeK_length_enc
import Theorems.Thm_Groundwork_Decode_length_enc
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_VariableBound_Paper_clauseCount
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open PairsToBound
open Turing Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg Wrap MainTheoremForms
open Sat3 (CNF)
namespace PairsToBound
theorem _root_.solution {k n : ℕ} {φ : CNF n} (hk : 1 ≤ k) (hn : 2 ≤ n) (hφ : SatK.IsKCNF k φ) : (SatM.enc k φ).length + 1 ≤ n ^ (8 * k) := by
  rw [End.length_enc]
  obtain ⟨a, ha⟩ : ∃ a, a = n ^ k := ⟨_, rfl⟩
  have e2 : n ^ (2 * k) = a ^ 2 := by rw [ha, ← pow_mul, Nat.mul_comm]
  have e3 : n ^ (3 * k) = a ^ 3 := by rw [ha, ← pow_mul, Nat.mul_comm]
  have e8 : n ^ (8 * k) = a ^ 8 := by rw [ha, ← pow_mul, Nat.mul_comm]
  have hna : n ≤ a := by
    rw [ha]
    exact Nat.le_self_pow (by omega) n
  have hka : k ≤ a := by
    rw [ha]
    exact (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left hn k)
  have hm : φ.length ≤ a ^ 3 := e3 ▸ (VariableBound.Paper.clauseCount k n φ hφ).trans (clauseCountPow_of_two_le k hn)
  have hL : Nat.log2 (2 * n) + 1 ≤ a ^ 2 := by
    have h1 : Nat.log2 (2 * n) < 2 * n := by
      rw [Nat.log2_eq_log_two]
      exact Nat.log_lt_self 2 (by omega)
    have h2 : 2 * n ≤ n * n := Nat.mul_le_mul_right n hn
    have h3 : n * n ≤ a * a := Nat.mul_le_mul hna hna
    rw [pow_two]
    omega
  have h6 : φ.length * (k * (Nat.log2 (2 * n) + 1)) ≤ a ^ 6 :=
    calc φ.length * (k * (Nat.log2 (2 * n) + 1)) ≤ a ^ 3 * (a * a ^ 2) := Nat.mul_le_mul hm (Nat.mul_le_mul hka hL)
      _ = a ^ 6 := by ring
  have h5 : 2 ^ 5 ≤ a ^ 5 := Nat.pow_le_pow_left (hn.trans hna) 5
  have h7 : k + n + 3 ≤ a ^ 6 :=
    calc k + n + 3 ≤ 2 ^ 5 * a := by omega
      _ ≤ a ^ 5 * a := Nat.mul_le_mul_right a h5
      _ = a ^ 6 := by ring
  have h8 : 2 * a ^ 6 ≤ a ^ 8 :=
    calc 2 * a ^ 6 ≤ a ^ 2 * a ^ 6 := Nat.mul_le_mul_right _ ((by norm_num : 2 ≤ 2 ^ 2).trans (Nat.pow_le_pow_left (hn.trans hna) 2))
      _ = a ^ 8 := by ring
  rw [e8]
  omega
end PairsToBound
