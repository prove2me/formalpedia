-- Prove2me | solution 1 for VariableBound.Fld.Quot.exists_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:08:07.640072+00:00
-- url     : https://prove2.me/submissions/3d008df5-18c8-4f1a-a1fa-cddf159df448

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
theorem _root_.solution (s : ℕ) (hs : 1 ≤ s) : ∃ f : (ZMod 2)[X], f.Monic ∧ Irreducible f ∧ f.natDegree = s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨α, hα⟩ := Field.exists_primitive_element_of_finite_top (ZMod 2) (GaloisField 2 s)
  have hint : IsIntegral (ZMod 2) α := Algebra.IsIntegral.isIntegral α
  refine ⟨minpoly (ZMod 2) α, minpoly.monic hint, minpoly.irreducible hint, ?_⟩
  rw [(Field.primitive_element_iff_minpoly_natDegree_eq (ZMod 2) α).mp hα, GaloisField.finrank 2 (by omega)]
end Quot
end VariableBound.Fld
