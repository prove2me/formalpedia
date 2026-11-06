-- Prove2me | solution 1 for SparsifyThenCount.eD_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:02:57.154969+00:00
-- url     : https://prove2.me/submissions/bcea0ee9-83d7-4cd1-bdf0-c9623ffd8241

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyThenCount_Defs
import Definitions.Def_VariableBound_Cert_Top
import Definitions.Def_UniformInK_Cert_Top
import Definitions.Def_ClauseBound_ParityChecks_CertTopOL
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_SparsifyThenCount_CertTop
import Theorems.Thm_SparsifyThenCount_planD_polyT
import Theorems.Thm_ClauseBound_Alg_Decode_stCertDecM
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_Unary_of_length
import Theorems.Thm_Groundwork_Unary_poly
import Theorems.Thm_PaddedDescent_F_CertNet_nU
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] PaddedDescent.F.CertNet.nU



set_option autoImplicit false
section
section
open SparsifyThenCount
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop PaddedDescent.F.CertEval CountKSatRate CountKSatRate.Cert ClauseBound.Alg ClauseBound.Alg.CertTop
open ClauseBound.TopN ClauseBound.TopN.Cert ClauseBound.ParityChecks UniformInK UniformInK.CertTop VariableBound VariableBound.CertTop SparsificationLemma
namespace SparsifyThenCount
theorem _root_.solution {Idx : Type} [Enc Idx] (S : Solver Idx) (hP : S.Poly) {pick : U → U × Idx} {slU : U → U} (hpick : PolyT pick) (hsl : PolyT slU) :
    PolyT (eD S pick slU) := by
  have hn0 : Unary nU := Unary.of_length (PolyT.fst Decode.stCertDecM.2)
  unfold eD
  exact PolyT.optionGetD (planD_polyT S hP hpick hsl) hn0.poly
end SparsifyThenCount
