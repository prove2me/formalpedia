-- Prove2me | solution 1 for VariableBound.CertTop.planAtD_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:40:29.41546+00:00
-- url     : https://prove2.me/submissions/faea7016-f6f2-40e4-9655-fc2e39fbfe00

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_Defs
import Definitions.Def_VariableBound_Net_CertEv
import Definitions.Def_UniformInK_Cert_Top
import Definitions.Def_ClauseBound_ParityChecks_CertTopOL
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_VariableBound_Cert_Top
import Theorems.Thm_VariableBound_CertTop_restD_polyT
import Theorems.Thm_VariableBound_CertTop_needNetC_polyT
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_QU_comp
import Theorems.Thm_ClauseBound_ParityChecks_CertTopOL_LD_polyT
import Theorems.Thm_ClauseBound_TopN_Cert_lamS_unary
import Theorems.Thm_ClauseBound_TopN_Cert_needNetC_polyT
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
import Theorems.Thm_Groundwork_Unary_poly
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
import Theorems.Thm_P2M_Groundwork_PolyT_ite__226169acf219
import Theorems.Thm_P2M_Groundwork_PolyT_size__c8c8eb1b342f
import Theorems.Thm_P2M_Groundwork_PolyT_some__e6a32bd6af45
import Theorems.Thm_UniformInK_CertTop_blockU_unary
import Theorems.Thm_UniformInK_CertTop_powBetaU_polyT
import Theorems.Thm_VariableBound_Net_CertEv_BbD_unary
import Theorems.Thm_VariableBound_Net_CertEv_PbD_unary
import Theorems.Thm_VariableBound_Net_CertEv_UbD_unary
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] P2M_Groundwork_PolyT_ite__226169acf219
attribute [local fun_prop] P2M_Groundwork_PolyT_size__c8c8eb1b342f
attribute [local fun_prop] P2M_Groundwork_PolyT_some__e6a32bd6af45



set_option autoImplicit false
section
section
open VariableBound VariableBound.CertTop
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop PaddedDescent.F.CertEval CountKSatRate CountKSatRate.Cert ClauseBound.Alg ClauseBound.Alg.CertTop
open ClauseBound.TopN ClauseBound.ParityChecks UniformInK UniformInK.CertTop VariableBound.Net VariableBound.Net.CertEv
open ClauseBound.TopN.Cert (lamS_unary)
open ClauseBound.ParityChecks.CertTopOL (LD_polyT)
variable {α : Type} [Enc α]
variable {Idx : Type} [Enc Idx] (S : Solver Idx)
namespace VariableBound.CertTop
theorem _root_.solution (hP : S.Poly) {k n s : α → ℕ} {i : α → Idx} (hk : Unary k) (hn : Unary n) (hi : PolyT i) (hs : Unary s) :
    PolyT fun x => planAtD S (k x) (n x) (i x) (s x) := by
  have hK : Unary fun x => S.K (i x) := hP.K.comp hi
  have hD := blockU_unary hk hn hs
  have hU := UbD_unary hk hK hn hD
  have hQ := PbD_unary hK hn hD
  have hr := restD_polyT hk hK hn hs
  have hnet := needNetC_polyT S hP (b := fun x => List.replicate (n x) ()) hn hi hU hQ (BbD_unary hk hn)
  have hk' : PolyT k := hk.poly
  have hn' : PolyT n := hn.poly
  have hs' : PolyT s := hs.poly
  have hpow := powBetaU_polyT hk hs
  have hc1 : PolyT fun x => decide (s0U (k x) ≤ s x) := by
    unfold s0U
    exact PolyT.decide_le ((PolyT.const 2).mul (PolyT.size' hk')) hs'
  have hc2 : PolyT fun x => decide (2 ^ betaU (k x) (s x) ≤ n x + 1) := PolyT.decide_le hpow (PolyT.add hn' (PolyT.const 1))
  have hc3 : PolyT fun x => decide (29 * LD (2 ^ betaU (k x) (s x)) + 19 ≤ n x) :=
    PolyT.decide_le (((PolyT.const 29).mul (LD_polyT hpow)).add (PolyT.const 19)) hn'
  have hsum : PolyT fun q : α × ℕ => q.2 + restD (k q.1) (S.K (i q.1)) (n q.1) (s q.1) :=
    PolyT.add PolyT.id'.snd (PolyT.comp (f := fun x => restD (k x) (S.K (i x)) (n x) (s x)) hr PolyT.id'.fst)
  have hn2 : PolyT fun q : α × ℕ => n q.1 := PolyT.comp (f := n) hn' PolyT.id'.fst
  have hin : PolyT fun x => (needNetC S (List.replicate (n x) ()) (i x) (UbD (k x) (S.K (i x)) (n x) (blockU (k x) (n x) (s x)))
      (PbD (S.K (i x)) (n x) (blockU (k x) (n x) (s x))) (BbD (k x) (n x))).bind fun v =>
      if v + restD (k x) (S.K (i x)) (n x) (s x) ≤ n x then some (v + restD (k x) (S.K (i x)) (n x) (s x)) else none :=
    PolyT.optionBind (PolyT.ite' (PolyT.decide_le hsum hn2) (PolyT.some' hsum) (PolyT.const none)) hnet
  unfold planAtD
  exact PolyT.ite' (PolyT.decide_and hc1 (PolyT.decide_and hc2 hc3)) hin (PolyT.const none)
end VariableBound.CertTop
