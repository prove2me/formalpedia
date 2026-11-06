-- Prove2me | solution 1 for RecursionToBound.planAt_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:28:02.990634+00:00
-- url     : https://prove2.me/submissions/302a2ab1-f4ef-4fe4-8ed9-21c0aa412145

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Cert_Thresholds
import Definitions.Def_VariableBound_Cert_Top
import Definitions.Def_VariableBound_Net_CertEv
import Definitions.Def_UniformInK_Cert_Top
import Definitions.Def_ClauseBound_TopN_Cert
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_PaddedDescent_F_CertEval
import Definitions.Def_ToTuring_Poly_NetFun
import Definitions.Def_RecursionToBound_Cert_Exponent
import Theorems.Thm_RecursionToBound_needWalk_polyT
import Theorems.Thm_RecursionToBound_needOutputsC_polyT
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_QU_comp
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_poly
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
import Theorems.Thm_P2M_Groundwork_PolyT_ite__226169acf219
import Theorems.Thm_P2M_Groundwork_PolyT_some__e6a32bd6af45
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] P2M_Groundwork_PolyT_ite__226169acf219
attribute [local fun_prop] P2M_Groundwork_PolyT_some__e6a32bd6af45



set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F PaddedDescent.F.CertEval CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Cert ClauseBound.ParityChecks UniformInK UniformInK.CertTop VariableBound VariableBound.Net VariableBound.Net.CertEv VariableBound.CertTop SparsificationLemma
variable {α : Type} [Enc α]
variable {Idx : Type} [Enc Idx] (S : Solver Idx)
namespace RecursionToBound
theorem _root_.solution (hP : S.Poly) (n₁ : ℕ) {k n : α → ℕ} {i : α → Idx} {r : α → ℕ × ℕ} (hk : Unary k) (hn : Unary n) (hi : PolyT i) (hr : PolyT r) :
    PolyT fun x => planAt S n₁ (k x) (n x) (i x) (r x) := by
  have hn' := hn.poly
  have hout := needOutputsC_polyT S hP (b := fun x => List.replicate (n x) ()) hn hk hr hi hn
  have hw := needWalk_polyT hk hr hn'
  have hsum : PolyT fun q : α × ℕ => q.2 + needWalk (k q.1) (r q.1) (n q.1) :=
    PolyT.add PolyT.id'.snd (PolyT.comp (f := fun x => needWalk (k x) (r x) (n x)) hw PolyT.id'.fst)
  have hn2 : PolyT fun q : α × ℕ => n q.1 := PolyT.comp (f := n) hn' PolyT.id'.fst
  unfold planAt
  exact PolyT.ite' (PolyT.decide_le (PolyT.const n₁) hn')
    (PolyT.optionBind (PolyT.ite' (PolyT.decide_le hsum hn2) (PolyT.some' hsum) (PolyT.const none)) hout) (PolyT.const none)
end RecursionToBound
