-- Prove2me | solution 1 for VariableBound.Fld.decW_surj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:13:48.749242+00:00
-- url     : https://prove2.me/submissions/cf500ce5-3184-4b92-867a-37fc2f1766a5

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
import Theorems.Thm_VariableBound_Fld_Quot_bitR_decide
import Theorems.Thm_VariableBound_Fld_Quot_getD_ofFn
import Theorems.Thm_VariableBound_Fld_bitsW_decW

set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld
open Polynomial
open VariableBound.Fld.Quot
namespace VariableBound.Fld
theorem _root_.solution (g : List Bool) (z : FW g) : ∃ w : List Bool, w.length = g.length ∧ decW g w = z := by
  refine ⟨List.ofFn fun i => decide (bitsW g z i = 1), List.length_ofFn, (bitsW g).injective (funext fun i => ?_)⟩
  rw [bitsW_decW g _ List.length_ofFn, getD_ofFn, bitR_decide]
end VariableBound.Fld
