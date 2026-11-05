-- Prove2me | solution 1 for UniformInK.Time.length_enc_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:04:22.389346+00:00
-- url     : https://prove2.me/submissions/d551c14f-71fb-4a0f-9f08-5c9883211755

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_ClauseBound_TopN_End
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_WidthK_Decode
import Definitions.Def_UniformInK_Top_Time
import Theorems.Thm_ClauseBound_Alg_End_length_enc_succ_le
import Theorems.Thm_Groundwork_DecodeK_length_enc_succ_le
import Theorems.Thm_Groundwork_Decode_length_enc_succ_le
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open UniformInK
open Groundwork PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.Alg.End ClauseBound.TopN ClauseBound.TopN.End
open UniformInK.Time
namespace UniformInK.Time
theorem _root_.solution {k n : ℕ} {φ : Sat3.CNF n} (hk : 1 ≤ k) (h : SatK.IsKCNF k φ) : (SatM.enc k φ).length + 1 ≤ (n + 2) ^ (5 * k) := by
  have h1 : (SatK.enc k φ).length + 1 ≤ (k * 2 ^ k + 1) * (n + 2) ^ (k + 1) := DecodeK.length_enc_succ_le (φ := φ) h
  have h2 : (SatM.enc k φ).length = k + 1 + (SatK.enc k φ).length := by
    unfold SatM.enc
    rw [List.length_append, List.length_cons, List.length_replicate]
    omega
  have hb : 2 ≤ n + 2 := by omega
  have hkk : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  have h3 : (2 : ℕ) ^ k ≤ (n + 2) ^ k := Nat.pow_le_pow_left hb k
  have h4 : k * 2 ^ k + 1 ≤ (n + 2) ^ (2 * k) := by
    calc k * 2 ^ k + 1 ≤ 2 ^ k * 2 ^ k := by nlinarith [Nat.one_le_two_pow (n := k)]
      _ ≤ (n + 2) ^ k * (n + 2) ^ k := Nat.mul_le_mul h3 h3
      _ = (n + 2) ^ (2 * k) := by rw [← pow_add]; congr 1; omega
  have h5 : (k * 2 ^ k + 1) * (n + 2) ^ (k + 1) ≤ (n + 2) ^ (3 * k + 1) := by
    calc (k * 2 ^ k + 1) * (n + 2) ^ (k + 1) ≤ (n + 2) ^ (2 * k) * (n + 2) ^ (k + 1) := Nat.mul_le_mul_right _ h4
      _ = (n + 2) ^ (3 * k + 1) := by rw [← pow_add]; congr 1; omega
  have h6 : k + 1 ≤ (n + 2) ^ (3 * k + 1) := (hkk.trans h3).trans (Nat.pow_le_pow_right (by omega) (by omega))
  calc (SatM.enc k φ).length + 1 ≤ 2 * (n + 2) ^ (3 * k + 1) := by omega
    _ ≤ (n + 2) * (n + 2) ^ (3 * k + 1) := Nat.mul_le_mul_right _ hb
    _ = (n + 2) ^ (3 * k + 2) := by rw [← pow_succ']
    _ ≤ (n + 2) ^ (5 * k) := Nat.pow_le_pow_right (by omega) (by omega)
end UniformInK.Time
