-- Prove2me | solution 1 for RecursionToBound.needAtC_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:55:42.045352+00:00
-- url     : https://prove2.me/submissions/bc104732-8170-4f1f-abf1-db156b1f3a5f

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
import Theorems.Thm_RecursionToBound_optionMap_add_two
import Theorems.Thm_RecursionToBound_nPrMax_polyT
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_QU_comp
import Theorems.Thm_ClauseBound_TopN_Cert_needNetC_polyT
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
import Theorems.Thm_Groundwork_Unary_poly
import Theorems.Thm_P2M_Groundwork_PolyT_size__c8c8eb1b342f
import Theorems.Thm_VariableBound_CertTop_needNetC_polyT
import Theorems.Thm_VariableBound_Net_CertEv_BbD_unary
import Theorems.Thm_VariableBound_Net_CertEv_PbD_unary
import Theorems.Thm_VariableBound_Net_CertEv_UbD_unary
import Theorems.Thm_VariableBound_Net_CertEv_sbMax_unary
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] P2M_Groundwork_PolyT_size__c8c8eb1b342f



set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F PaddedDescent.F.CertEval CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Cert ClauseBound.ParityChecks UniformInK UniformInK.CertTop VariableBound VariableBound.Net VariableBound.Net.CertEv VariableBound.CertTop SparsificationLemma
variable {α : Type} [Enc α]
variable {Idx : Type} [Enc Idx] (S : Solver Idx)
namespace RecursionToBound
theorem _root_.solution (hP : S.Poly) {b : α → U} {k n Δ : α → ℕ} {i : α → Idx} (hb : PolyT b) (hk : Unary k) (hi : PolyT i) (hn : Unary n) (hΔ : Unary Δ) :
    PolyT fun x => needAtC S (b x) (k x) (i x) (n x) (Δ x) := by
  have hK : Unary fun x => S.K (i x) := hP.K.comp hi
  have hnet := needNetC_polyT S hP hb hi (UbD_unary hk hK hn hΔ) (PbD_unary hK hn hΔ) (BbD_unary hk hn)
  have hA : PolyT fun x => Nat.size (nPrMax (S.K (i x)) (n x) (Δ x)) := PolyT.size' (nPrMax_polyT hK hn hΔ)
  have hn' := hn.poly
  have hB : PolyT fun x => Nat.size (8 * (10 * n x + 1) * (sbMax (Δ x) + 1) * (Nat.size (Δ x * n x) + 2) + 8) :=
    PolyT.size' (((((PolyT.const 8).mul (((PolyT.const 10).mul hn').add (PolyT.const 1))).mul ((sbMax_unary hΔ).poly.add (PolyT.const 1))).mul
      ((PolyT.size' (hΔ.poly.mul hn')).add (PolyT.const 2))).add (PolyT.const 8))
  have h := optionMap_add_two hnet hA hB
  unfold needAtC
  exact h
end RecursionToBound
