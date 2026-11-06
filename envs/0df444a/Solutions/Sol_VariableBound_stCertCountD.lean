-- Prove2me | solution 1 for VariableBound.stCertCountD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:16:52.821919+00:00
-- url     : https://prove2.me/submissions/ace09d92-9c5e-4961-afac-4d543af6d46d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Count_Defs
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_VariableBound_Count_Cert
import Theorems.Thm_VariableBound_Count_countD_polyT
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_Unary_of_length
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f



set_option autoImplicit false
section
section
open VariableBound
open Groundwork Groundwork.Prog PaddedDescent.F
namespace VariableBound
theorem _root_.solution (hEv : Net.StCertEvD) (hS : StCertSearchD) (hFam : Fld.StCertFamD) (hPar : StCertParam) : StCertCountD := by
  intro Idx _ S hP
  exact Count.countD_polyT hEv hS hFam hPar hP (k := fun x : U × U × Idx × (U × U) × Fml => x.1.length) (Unary.of_length PolyT.id'.fst)
    (Unary.of_length PolyT.id'.snd.snd.snd.fst.fst) (Unary.of_length PolyT.id'.snd.snd.snd.fst.snd) PolyT.id'.snd.fst PolyT.id'.snd.snd.fst PolyT.id'.snd.snd.snd.snd
end VariableBound
