-- Prove2me | solution 1 for SparsifyThenCount.stCertBDG
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:50:57.20691+00:00
-- url     : https://prove2.me/submissions/1c85d6fa-c7d7-4b58-ac65-77295789a98c

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
import Theorems.Thm_SparsifyThenCount_eBD_polyT
import Theorems.Thm_ClauseBound_Alg_CertTop_stCertM
import Theorems.Thm_ClauseBound_Alg_CertTop_stCertSatK
import Theorems.Thm_ClauseBound_Alg_Decode_stCertDecM
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_QU_comp
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_cond__4c673073da15
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
import Theorems.Thm_PaddedDescent_F_certRebalG
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] P2M_Groundwork_PolyT_cond__4c673073da15
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f



set_option autoImplicit false
section
section
open SparsifyThenCount
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK UniformInK.CertBoth VariableBound
namespace SparsifyThenCount
theorem _root_.solution (h : StCertDG) : StCertBDG := by
  intro Θ Lc hΘ Idx _ S hS pick slU hpick hsl
  have hADG := h Θ Lc hΘ Idx S hS pick slU hpick hsl
  have hAM := (CertTop.stCertM Decode.stCertDecM CertTop.stCertSatK certRebalG Idx S hS pick hpick).1
  have h2 : PolyT fun p : List Bool × U => useMD S pick slU p.1 := PolyT.comp (useMD_polyT S hS hpick hsl) PolyT.id'.fst
  exact ⟨PolyT.cond' h2 hAM hADG, eBD_polyT S hS hpick hsl⟩
end SparsifyThenCount
