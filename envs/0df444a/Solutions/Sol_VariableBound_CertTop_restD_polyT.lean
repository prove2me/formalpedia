-- Prove2me | solution 1 for VariableBound.CertTop.restD_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:14:06.633204+00:00
-- url     : https://prove2.me/submissions/9d5c92a3-5901-471f-a3ea-4ca208b71425

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_Defs
import Definitions.Def_VariableBound_Net_CertEv
import Definitions.Def_UniformInK_Cert_Top
import Definitions.Def_ClauseBound_ParityChecks_CertTopOL
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_VariableBound_Cert_Top
import Theorems.Thm_VariableBound_CertTop_restD_aux
import Theorems.Thm_ClauseBound_ParityChecks_CertTopOL_LD_polyT
import Theorems.Thm_ClauseBound_TopN_Cert_lamS_unary
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
import Theorems.Thm_Groundwork_Unary_poly
import Theorems.Thm_P2M_Groundwork_PolyT_size__c8c8eb1b342f
import Theorems.Thm_UniformInK_CertTop_betaU_unary
import Theorems.Thm_UniformInK_CertTop_blockU_unary
import Theorems.Thm_VariableBound_Net_CertEv_objMax_unary
import Theorems.Thm_VariableBound_Net_CertEv_sbMax_unary
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] P2M_Groundwork_PolyT_size__c8c8eb1b342f



set_option autoImplicit false
section
section
open VariableBound VariableBound.CertTop
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop PaddedDescent.F.CertEval CountKSatRate CountKSatRate.Cert ClauseBound.Alg ClauseBound.Alg.CertTop
open ClauseBound.TopN ClauseBound.ParityChecks UniformInK UniformInK.CertTop VariableBound.Net VariableBound.Net.CertEv
open ClauseBound.TopN.Cert (lamS_unary)
open ClauseBound.ParityChecks.CertTopOL (LD_polyT)
variable {α : Type} [Enc α]
variable {k K n s : α → ℕ}
namespace VariableBound.CertTop
theorem _root_.solution (hk : Unary k) (hK : Unary K) (hn : Unary n) (hs : Unary s) : PolyT fun x => restD (k x) (K x) (n x) (s x) := by
  have hD := blockU_unary hk hn hs
  have hn' := hn.poly
  unfold restD
  exact restD_aux hk.poly hK.poly (PolyT.size' (objMax_unary hn hD).poly)
    (PolyT.size' (((((PolyT.const 8).mul (((PolyT.const 10).mul hn').add (PolyT.const 1))).mul ((sbMax_unary hD).poly.add (PolyT.const 1))).mul
      ((PolyT.size' (hD.poly.mul hn')).add (PolyT.const 2))).add (PolyT.const 8)))
    (betaU_unary hk hs).poly (PolyT.size' hn') hn' (pow_polyT (PolyT.const 2) hs)
end VariableBound.CertTop
