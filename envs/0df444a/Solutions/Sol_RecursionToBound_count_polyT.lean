-- Prove2me | solution 1 for RecursionToBound.count_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:14:20.105172+00:00
-- url     : https://prove2.me/submissions/e228de45-46fb-4dd5-8624-9b23526e909c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Cert_Exponent
import Definitions.Def_VariableBound_MainPrinted
import Definitions.Def_StepSparsify_CertWalk
import Definitions.Def_CountKSatRate_Cert
import Definitions.Def_CountKSat_Poly
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Poly_NetFun
import Definitions.Def_RecursionToBound_Cert_Top
import Theorems.Thm_RecursionToBound_countAll_polyT
import Theorems.Thm_ClauseBound_Alg_Decode_stCertDecM
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_QU_comp
import Theorems.Thm_ClauseBound_ParityChecks_CertOL_CU_comp
import Theorems.Thm_CountKSatRate_Cert_bruteN_polyT_aux
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_count
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_prodMk
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_cond__4c673073da15
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
import Theorems.Thm_PaddedDescent_F_CertNet_nU
import Theorems.Thm_RecursionToBound_idxU_polyT
import Theorems.Thm_RecursionToBound_numU_polyT
import Theorems.Thm_RecursionToBound_plan_polyT
import Theorems.Thm_RecursionToBound_powWidthCut_unary
import Theorems.Thm_RecursionToBound_widthCut_unary
import Theorems.Thm_VariableBound_Net_Main_p
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.count
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.prodMk
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] P2M_Groundwork_PolyT_cond__4c673073da15
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] PaddedDescent.F.CertNet.nU



set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F CountKSatRate CountKSatRate.Cert ClauseBound.Alg UniformInK VariableBound SparsificationLemma
variable {α : Type} [Enc α]
variable {Idx : Type} [Enc Idx] (S : Solver Idx)
namespace RecursionToBound
theorem _root_.solution (hC : StCertCountD) (hP : S.Poly) (n₁ : ℕ) {pick : U → U × Idx} {num : U × U → ℕ × ℕ} (hpick : PolyT pick) (hnum : PolyT num) : PolyT (count S n₁ pick num) := by
  have hfst : PolyT fun p : List Bool × U => p.1 := PolyT.id'.fst
  have hd : PolyT fun p : List Bool × U => fmlOf p.1 := PolyT.comp Decode.stCertDecM.2 hfst
  have hp : PolyT fun p : List Bool × U => p.2 := PolyT.id'.snd
  have hall : PolyT fun p : List Bool × U => countAll S (kcU (widthU p.1) (nU p.1)) (numU S pick num p.1) (idxU pick p.1) (fmlOf p.1) p.2 :=
    countAll_polyT S hC hP (widthCut_unary.comp hfst) (powWidthCut_unary.comp hfst) (PolyT.comp (numU_polyT S hP hpick hnum) hfst) (PolyT.comp (idxU_polyT hpick) hfst) hd hp
  have hbr : PolyT bruteU := by
    have h := bruteN_polyT_aux hd (pad := fun p : List Bool × U => p.2) hp
    unfold bruteU
    exact h
  have hno : PolyT fun p : List Bool × U => (plan S n₁ pick num p.1).isNone := PolyT.optionIsNone (PolyT.comp (plan_polyT S hP n₁ hpick hnum) hfst)
  unfold count
  exact PolyT.comp outW_polyT (PolyT.prodMk hd (PolyT.cond' hno hbr hall))
end RecursionToBound
