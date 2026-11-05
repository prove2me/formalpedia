-- Prove2me | solution 1 for VariableBound.Fld.Quot.bitsW_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:07:59.355074+00:00
-- url     : https://prove2.me/submissions/bb6d9295-b22c-4d6e-94a1-e521be129f70

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
namespace Quot
theorem _root_.solution (g : List Bool) (p : (ZMod 2)[X]) (i : Fin g.length) : bitsW g (AdjoinRoot.mk (modP g) p) i = (p %ₘ modP g).coeff i.val := by
  rw [bitsW, LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, Module.Basis.equivFun_apply, AdjoinRoot.powerBasisAux'_repr_apply_to_fun,
    AdjoinRoot.modByMonicHom_mk]
  rfl
end Quot
end VariableBound.Fld
