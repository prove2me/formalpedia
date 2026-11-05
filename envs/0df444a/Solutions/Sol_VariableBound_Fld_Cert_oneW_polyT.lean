-- Prove2me | solution 1 for VariableBound.Fld.Cert.oneW_polyT
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T02:22:59.848235+00:00
-- url     : https://prove2.me/submissions/91a65666-2982-4f64-a26f-63a2c078925b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Defs
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Mathlib.Data.List.Find
import Definitions.Def_VariableBound_Field_Cert
set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld VariableBound.Fld.Cert
open Groundwork PaddedDescent.F ClauseBound.ParityChecks.CertLib
variable {α : Type} [Enc α]

theorem solution {g : α → List Bool} (hg : PolyT g) : PolyT fun c => oneW (g c) := by
  have hn : Unary fun c => (g c).length - 1 :=
    unary_sub (unary_length hg) (PolyT.const 1)
  have hr : PolyT fun c => List.range ((g c).length - 1) := range_polyT hn
  have hm : PolyT fun c => (List.range ((g c).length - 1)).map (fun _ => false) :=
    PolyT.map (PolyT.const false) hr
  have hc : PolyT fun c => true :: (List.range ((g c).length - 1)).map (fun _ => false) :=
    PolyT.cons' (PolyT.const true) hm
  refine hc.congr ?_
  intro c
  unfold oneW
  cases h : g c with
  | nil => simp
  | cons b l => simp
