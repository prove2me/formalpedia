-- Prove2me | solution 1 for VariableBound.Fld.Cert.length_mulX_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:19:27.539654+00:00
-- url     : https://prove2.me/submissions/1de45e51-9651-449f-9841-40eb93215186

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Defs
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Mathlib.Data.List.Find
import Definitions.Def_VariableBound_Field_Cert
import Theorems.Thm_VariableBound_Fld_Cert_length_xorW
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld VariableBound.Fld.Cert
open Groundwork PaddedDescent.F ClauseBound.ParityChecks.CertLib
variable {α : Type} [Enc α]
namespace VariableBound.Fld.Cert
theorem _root_.solution (g w : List Bool) : (mulX g w).length ≤ w.length := by
  unfold mulX
  split_ifs
  · rw [length_xorW, List.length_take, List.length_cons]
    omega
  · rw [List.length_take, List.length_cons]
    omega
end VariableBound.Fld.Cert
