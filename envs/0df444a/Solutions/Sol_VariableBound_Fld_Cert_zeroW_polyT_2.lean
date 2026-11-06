-- Prove2me | solution 2 for VariableBound.Fld.Cert.zeroW_polyT
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:21:40.552414+00:00
-- url     : https://prove2.me/submissions/63c5dad9-3fff-40a3-bcaf-dbb27f746bab

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Defs
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Mathlib.Data.List.Find
import Definitions.Def_VariableBound_Field_Cert
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_const
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.const
set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld VariableBound.Fld.Cert
open Groundwork PaddedDescent.F ClauseBound.ParityChecks.CertLib
variable {α : Type} [Enc α]

theorem solution {g : α → List Bool} (hg : PolyT g) : PolyT fun c => zeroW (g c) := by
  unfold zeroW
  fun_prop
