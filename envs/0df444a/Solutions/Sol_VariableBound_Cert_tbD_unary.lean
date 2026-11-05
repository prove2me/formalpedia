-- Prove2me | solution 1 for VariableBound.Cert.tbD_unary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:41:28.809489+00:00
-- url     : https://prove2.me/submissions/c9125433-8d95-4058-baa3-0252fd7a65ba

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Params_Defs
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_VariableBound_Params_Cert
import Theorems.Thm_VariableBound_Cert_filter_range_polyT
import Theorems.Thm_VariableBound_Cert_size_unary
import Theorems.Thm_ClauseBound_Alg_CertGridG_unary_min_right
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_QU_comp
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_unary_min_right
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_PolyT_pow_unary
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_PolyT_two_pow
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
import Theorems.Thm_Groundwork_Unary_of_length
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
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
theorem _root_.solution {m nb rb : α → ℕ} (hm : PolyT m) (hnb : PolyT nb) (hrb : Unary rb) : Unary fun x => tbD (m x) (nb x) (rb x) := by
  have hN : Unary fun x => Nat.size (m x) + rb x + 1 := ((size_unary hm).add hrb).add (Unary.const 1)
  have hmin : Unary fun p : α × ℕ => min p.2 (Nat.size (m p.1) + rb p.1 + 1) := unary_min_right PolyT.id'.snd (hN.comp PolyT.id'.fst)
  have hnb' : PolyT fun p : α × ℕ => 15 * nb p.1 := (PolyT.const 15).mul (PolyT.comp hnb PolyT.id'.fst)
  have hrb' : Unary fun p : α × ℕ => rb p.1 := hrb.comp PolyT.id'.fst
  exact Unary.of_length (filter_range_polyT (f := fun x c => decide (¬ m x * (15 * nb x + 16) ^ rb x ≤ 2 ^ c * (15 * nb x) ^ rb x)) hN
    (PolyT.decide_not (PolyT.decide_le ((PolyT.comp hm PolyT.id'.fst).mul (PolyT.pow_unary (hnb'.add (PolyT.const 16)) hrb'))
      ((PolyT.two_pow hmin).mul (PolyT.pow_unary hnb' hrb')))))
end VariableBound.Cert
