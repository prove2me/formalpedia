-- Prove2me | solution 1 for VariableBound.Fld.two_eq_zero_FW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:51:21.906599+00:00
-- url     : https://prove2.me/submissions/aaa53399-2bb4-4354-98b5-b070680cac67

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

set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld
open Polynomial
open VariableBound.Fld.Quot
namespace VariableBound.Fld
theorem _root_.solution (g : List Bool) : (2 : FW g) = 0 := by
  have h : (2 : ZMod 2) = 0 := by decide
  rw [← map_ofNat (algebraMap (ZMod 2) (FW g)) 2, h, map_zero]
end VariableBound.Fld
