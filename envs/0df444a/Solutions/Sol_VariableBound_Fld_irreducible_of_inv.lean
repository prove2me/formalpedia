-- Prove2me | solution 1 for VariableBound.Fld.irreducible_of_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:08:13.315012+00:00
-- url     : https://prove2.me/submissions/cdeb2def-a638-4791-ad89-0d1449d0590b

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
theorem _root_.solution (g : List Bool) (hg : 1 ≤ g.length) (h : ∀ z : FW g, z ≠ 0 → ∃ z', z * z' = 1) : Irreducible (modP g) := by
  have hnt : Nontrivial (FW g) := AdjoinRoot.nontrivial _ (by
    rw [degree_eq_natDegree (monic_modP g).ne_zero, natDegree_modP]
    exact_mod_cast (by omega : g.length ≠ 0))
  have hfield : IsField (FW g) := { exists_pair_ne := ⟨0, 1, zero_ne_one⟩, mul_comm := mul_comm, mul_inv_cancel := fun {a} ha => h a ha }
  have hmax : (Ideal.span {modP g}).IsMaximal := Ideal.Quotient.maximal_of_isField _ hfield
  exact ((Ideal.span_singleton_prime (monic_modP g).ne_zero).mp hmax.isPrime).irreducible
end VariableBound.Fld
