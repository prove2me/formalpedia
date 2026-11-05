-- Prove2me | solution 1 for VariableBound.Fld.decW_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:13:29.512095+00:00
-- url     : https://prove2.me/submissions/a43d4a4e-88ab-467b-ae5c-22860a4312b5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Alg
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Definitions.Def_VariableBound_Field_Quot
import Theorems.Thm_VariableBound_Fld_Quot_bitR_inj
import Theorems.Thm_VariableBound_Fld_bitsW_decW
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld
open Polynomial
open VariableBound.Fld.Quot
namespace VariableBound.Fld
theorem _root_.solution (g : List Bool) {w w' : List Bool} (hw : w.length = g.length) (hw' : w'.length = g.length) (h : decW g w = decW g w') : w = w' := by
  refine List.ext_getElem (hw.trans hw'.symm) fun i hi hi' => ?_
  have h1 := bitsW_decW g w hw ⟨i, hw ▸ hi⟩
  rw [h, bitsW_decW g w' hw'] at h1
  have h2 := bitR_inj h1
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi'] at h2
  exact h2.symm
end VariableBound.Fld
