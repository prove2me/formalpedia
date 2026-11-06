-- Prove2me | solution 1 for SparsifyThenCount.planD_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:49:25.615273+00:00
-- url     : https://prove2.me/submissions/a201fb8e-24fd-4588-9d33-c0b9906773c6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyThenCount_Defs
import Definitions.Def_VariableBound_Cert_Top
import Definitions.Def_UniformInK_Cert_Top
import Definitions.Def_ClauseBound_ParityChecks_CertTopOL
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_SparsifyThenCount_CertTop
import Theorems.Thm_ClauseBound_Alg_Decode_stCertDecM
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_QU_comp
import Theorems.Thm_ClauseBound_TopN_Cert_root17_polyT
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_Groundwork_Unary_of_length
import Theorems.Thm_PaddedDescent_F_CertNet_nU
import Theorems.Thm_VariableBound_CertTop_planAtD_polyT
attribute [local fun_prop] ClauseBound.TopN.Cert.root17_polyT
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] PaddedDescent.F.CertNet.nU



set_option autoImplicit false
section
section
open SparsifyThenCount
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop PaddedDescent.F.CertEval CountKSatRate CountKSatRate.Cert ClauseBound.Alg ClauseBound.Alg.CertTop
open ClauseBound.TopN ClauseBound.TopN.Cert ClauseBound.ParityChecks UniformInK UniformInK.CertTop VariableBound VariableBound.CertTop SparsificationLemma
namespace SparsifyThenCount
theorem _root_.solution {Idx : Type} [Enc Idx] (S : Solver Idx) (hP : S.Poly) {pick : U → U × Idx} {slU : U → U} (hpick : PolyT pick) (hsl : PolyT slU) :
    PolyT (planD S pick slU) := by
  have hd0 : PolyT fmlOf := Decode.stCertDecM.2
  have hk0 : Unary kU := Unary.of_length Decode.stCertDecM.1
  have hn0 : Unary nU := Unary.of_length hd0.fst
  have hlv0 : PolyT fun x : List Bool => pick (root17 (nU x)) := PolyT.comp hpick (root17_polyT hn0)
  exact planAtD_polyT S hP hk0 hn0 hlv0.snd (Unary.of_length (PolyT.comp hsl hlv0.fst))
end SparsifyThenCount
