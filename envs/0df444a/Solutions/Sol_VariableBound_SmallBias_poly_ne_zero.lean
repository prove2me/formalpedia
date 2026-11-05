-- Prove2me | solution 1 for VariableBound.SmallBias.poly_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:58:56.988758+00:00
-- url     : https://prove2.me/submissions/e2699d41-45bc-4395-b10c-ffa4fc217784

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppVariablesStatement
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic
import Definitions.Def_VariableBound_Family_SmallBias

set_option autoImplicit false
section
section
open VariableBound VariableBound.SmallBias
open Finset AppVariables
variable {F : Type} [Field F] {m : ℕ}
namespace VariableBound.SmallBias
theorem _root_.solution (V' : Finset (Fin m)) (hV : V'.Nonempty) : poly F V' ≠ 0 := by
  obtain ⟨E₀, hE₀⟩ := hV
  intro h0
  have hc : (poly F V').coeff E₀.val = 1 := by
    rw [poly, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_X_pow]
    rw [sum_eq_single E₀]
    · simp
    · intro E _ hne
      rw [if_neg]
      exact fun h => hne (Fin.ext h.symm)
    · exact fun h => absurd hE₀ h
  rw [h0, Polynomial.coeff_zero] at hc
  exact zero_ne_one hc
end VariableBound.SmallBias
