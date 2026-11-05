-- Prove2me | solution 1 for VariableBound.Cert.nbD_unary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:41:24.704956+00:00
-- url     : https://prove2.me/submissions/f019d92d-9f8d-41ee-b2da-fc0b5b20e4c7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Params_Defs
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_VariableBound_Params_Cert
import Theorems.Thm_VariableBound_Cert_filter_range_polyT
import Theorems.Thm_VariableBound_Cert_two_pow_log_le
import Theorems.Thm_VariableBound_Cert_nbD_le
import Theorems.Thm_ClauseBound_Alg_CertGridG_unary_min_right
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_QU_comp
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_log_unary
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_unary_min_right
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_PolyT_pow_unary
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_PolyT_two_pow
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
import Theorems.Thm_Groundwork_Unary_of_le
import Theorems.Thm_Groundwork_Unary_of_length
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f



set_option autoImplicit false
section
section
open VariableBound
open Groundwork AppVariables PaddedDescent.F ClauseBound.ParityChecks.CertLib
open VariableBound.Cert
variable {α : Type} [Enc α]
namespace VariableBound.Cert
theorem _root_.solution {n Δ : α → ℕ} (hn : Unary n) (hΔ : PolyT Δ) : Unary fun x => nbD (n x) (Δ x) := by
  have hN : Unary fun x => Nat.log 2 (n x) + 1 := (log_unary hn).add (Unary.const 1)
  have hmin : Unary fun p : α × ℕ => min p.2 (Nat.log 2 (n p.1) + 1) := unary_min_right PolyT.id'.snd (hN.comp PolyT.id'.fst)
  have hexp : Unary fun p : α × ℕ => 2 ^ min p.2 (Nat.log 2 (n p.1) + 1) :=
    Unary.of_le (((Unary.const 2).mul ((hn.comp PolyT.id'.fst).add (Unary.const 1)))) (PolyT.two_pow hmin) fun p =>
      calc 2 ^ min p.2 (Nat.log 2 (n p.1) + 1) ≤ 2 ^ (Nat.log 2 (n p.1) + 1) := Nat.pow_le_pow_right (by norm_num) (min_le_right _ _)
        _ = 2 * 2 ^ Nat.log 2 (n p.1) := pow_succ' _ _
        _ ≤ 2 * (n p.1 + 1) := Nat.mul_le_mul_left 2 (two_pow_log_le _)
  have hl : PolyT fun x => (List.range (Nat.log 2 (n x) + 1)).filter fun a => decide ((2 * Δ x) ^ 2 ^ a ≤ 2 ^ n x) :=
    filter_range_polyT (f := fun x a => decide ((2 * Δ x) ^ 2 ^ a ≤ 2 ^ n x)) hN
      (PolyT.decide_le (PolyT.pow_unary ((PolyT.const 2).mul (PolyT.comp hΔ PolyT.id'.fst)) hexp) (PolyT.two_pow (hn.comp PolyT.id'.fst)))
  exact Unary.of_le (hn.add (Unary.const 1)) (PolyT.two_pow (unary_sub (Unary.of_length hl) (PolyT.const 1))) fun x => nbD_le _ _
end VariableBound.Cert
