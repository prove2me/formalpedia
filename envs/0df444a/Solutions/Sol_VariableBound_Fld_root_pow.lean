-- Prove2me | solution 1 for VariableBound.Fld.root_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:12:10.958669+00:00
-- url     : https://prove2.me/submissions/d90f1b26-4715-441b-a46f-387c234ae6c1

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
import Theorems.Thm_VariableBound_Fld_two_eq_zero_FW
import Theorems.Thm_VariableBound_Fld_mk_polyW

set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld
open Polynomial
open VariableBound.Fld.Quot
namespace VariableBound.Fld
theorem _root_.solution (g : List Bool) : AdjoinRoot.root (modP g) ^ g.length = decW g g := by
  have h0 : AdjoinRoot.root (modP g) ^ g.length + decW g g = 0 := by
    have h : AdjoinRoot.mk (modP g) (X ^ g.length + polyW g) = 0 := AdjoinRoot.mk_self (f := modP g)
    rwa [map_add, map_pow, AdjoinRoot.mk_X, mk_polyW] at h
  have h2 : decW g g + decW g g = 0 := by rw [← two_mul, two_eq_zero_FW, zero_mul]
  calc AdjoinRoot.root (modP g) ^ g.length = AdjoinRoot.root (modP g) ^ g.length + (decW g g + decW g g) := by rw [h2, add_zero]
    _ = decW g g := by rw [← add_assoc, h0, zero_add]
end VariableBound.Fld
