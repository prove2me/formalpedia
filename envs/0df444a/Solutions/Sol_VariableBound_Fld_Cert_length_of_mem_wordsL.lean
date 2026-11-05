-- Prove2me | solution 1 for VariableBound.Fld.Cert.length_of_mem_wordsL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:33:10.074127+00:00
-- url     : https://prove2.me/submissions/c225f468-6ce1-419a-947c-630feadbb7ed

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Defs
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Mathlib.Data.List.Find
import Definitions.Def_VariableBound_Field_Cert
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_length_toWord
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local simp] Groundwork.length_toWord



set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld VariableBound.Fld.Cert
open Groundwork PaddedDescent.F ClauseBound.ParityChecks.CertLib
variable {α : Type} [Enc α]
namespace VariableBound.Fld.Cert
theorem _root_.solution {s : ℕ} {g : List Bool} (h : g ∈ wordsL s) : g.length = s := by
  obtain ⟨y, -, rfl⟩ := List.mem_map.1 h
  exact length_toWord s y
end VariableBound.Fld.Cert
