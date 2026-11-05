-- Prove2me | solution 1 for VariableBound.Fld.mk_polyW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:10:27.349439+00:00
-- url     : https://prove2.me/submissions/3b20a438-9960-40d6-ad7e-7435abd0ba23

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
import Theorems.Thm_VariableBound_Fld_map_decR

set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld
open Polynomial
open VariableBound.Fld.Quot
namespace VariableBound.Fld
theorem _root_.solution (g w : List Bool) : AdjoinRoot.mk (modP g) (polyW w) = decW g w := by
  rw [polyW, map_decR, AdjoinRoot.mk_X, decW]
end VariableBound.Fld
