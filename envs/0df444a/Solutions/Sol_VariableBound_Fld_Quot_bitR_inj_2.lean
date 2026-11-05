-- Prove2me | solution 2 for VariableBound.Fld.Quot.bitR_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:07:24.76276+00:00
-- url     : https://prove2.me/submissions/bcd641c6-1eeb-440f-8885-bb20d8ebbca1

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
namespace VariableBound.Fld.Quot
theorem _root_.solution {b b' : Bool} (h : bitR (ZMod 2) b = bitR (ZMod 2) b') : b = b' := by
  revert b b'
  decide
end VariableBound.Fld.Quot
