-- Prove2me | solution 1 for VariableBound.Fld.exists_irreducible_modP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:10:31.947513+00:00
-- url     : https://prove2.me/submissions/a0bef215-26e4-4ad9-8a15-36a833943832

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
import Theorems.Thm_VariableBound_Fld_Quot_exists_irreducible
import Theorems.Thm_VariableBound_Fld_Quot_eq_modP

set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld
open Polynomial
open VariableBound.Fld.Quot
namespace VariableBound.Fld
theorem _root_.solution (s : ℕ) (hs : 1 ≤ s) : ∃ g : List Bool, g.length = s ∧ Irreducible (modP g) := by
  obtain ⟨f, hm, hi, hd⟩ := exists_irreducible s hs
  refine ⟨List.ofFn fun i : Fin f.natDegree => decide (f.coeff i = 1), by rw [List.length_ofFn, hd], ?_⟩
  rw [eq_modP f hm]
  exact hi
end VariableBound.Fld
