-- Prove2me | solution 1 for SparsifyThenCount.eBD_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:40:36.124476+00:00
-- url     : https://prove2.me/submissions/8ca06f84-a931-4f27-ba6b-bd9b27101f51

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyThenCount_Defs
import Definitions.Def_SparsifyThenCount_CertTop
import Definitions.Def_UniformInK_Cert_Both
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_ClauseBound_Alg_CertTop
import Definitions.Def_PaddedDescent_Col_CertG
import Definitions.Def_SparsifyThenCount_CertBoth
import Theorems.Thm_SparsifyThenCount_useMD_polyT
import Theorems.Thm_ClauseBound_Alg_CertTop_stCertM
import Theorems.Thm_ClauseBound_Alg_CertTop_stCertSatK
import Theorems.Thm_ClauseBound_Alg_Decode_stCertDecM
import Theorems.Thm_P2M_Groundwork_PolyT_cond__4c673073da15
import Theorems.Thm_PaddedDescent_F_certRebalG
import Theorems.Thm_SparsifyThenCount_eD_polyT
attribute [local fun_prop] P2M_Groundwork_PolyT_cond__4c673073da15



set_option autoImplicit false
section
section
open SparsifyThenCount
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK UniformInK.CertBoth VariableBound
namespace SparsifyThenCount
theorem _root_.solution {Idx : Type} [Enc Idx] (S : Solver Idx) (hS : S.Poly) {pick : U → U × Idx} {slU : U → U} (hpick : PolyT pick) (hsl : PolyT slU) :
    PolyT (eBD S pick slU) :=
  PolyT.cond' (useMD_polyT S hS hpick hsl) (CertTop.stCertM Decode.stCertDecM CertTop.stCertSatK certRebalG Idx S hS pick hpick).2 (eD_polyT S hS hpick hsl)
end SparsifyThenCount
