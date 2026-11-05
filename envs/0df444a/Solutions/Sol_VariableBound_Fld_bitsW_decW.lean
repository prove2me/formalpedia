-- Prove2me | solution 1 for VariableBound.Fld.bitsW_decW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:12:01.727101+00:00
-- url     : https://prove2.me/submissions/ff2fce88-7d3b-4180-bc07-5ec1b295ccda

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
import Theorems.Thm_VariableBound_Fld_mk_polyW
import Theorems.Thm_VariableBound_Fld_Quot_bitsW_mk

set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld
open Polynomial
open VariableBound.Fld.Quot
namespace VariableBound.Fld
theorem _root_.solution (g w : List Bool) (hw : w.length = g.length) (i : Fin g.length) : bitsW g (decW g w) i = bitR (ZMod 2) (w.getD i.val false) := by
  have hdeg : (polyW w).degree < (modP g).degree := by
    rw [degree_eq_natDegree (monic_modP g).ne_zero, natDegree_modP, ← hw]
    exact degree_polyW_lt w
  rw [← mk_polyW, bitsW_mk, (modByMonic_eq_self_iff (monic_modP g)).mpr hdeg, coeff_polyW]
end VariableBound.Fld
