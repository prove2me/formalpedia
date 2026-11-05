-- Prove2me | solution 1 for VariableBound.Pairwise.pair_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:45:50.919515+00:00
-- url     : https://prove2.me/submissions/2abf6c7f-fe2e-45c4-ba0c-70a79aebcf00

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppVariablesStatement
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.LinearCombination
import Definitions.Def_VariableBound_Family_Pairwise

set_option autoImplicit false
section
section
open VariableBound VariableBound.Pairwise
open Finset AppVariables
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m s : ℕ}
omit [DecidableEq F] [Algebra (ZMod 2) F]
namespace VariableBound.Pairwise
theorem _root_.solution (θ θ' : F) (h : θ ≠ θ') : Function.Bijective fun p : F × F => (p.1 * θ + p.2, p.1 * θ' + p.2) := by
  refine Finite.injective_iff_bijective.1 fun p q hpq => ?_
  simp only [Prod.mk.injEq] at hpq
  obtain ⟨h1, h2⟩ := hpq
  have h3 : (p.1 - q.1) * (θ - θ') = 0 := by linear_combination h1 - h2
  have h4 : p.1 = q.1 := by
    rcases mul_eq_zero.1 h3 with h5 | h5
    · exact sub_eq_zero.1 h5
    · exact absurd (sub_eq_zero.1 h5) h
  refine Prod.ext h4 ?_
  rw [h4] at h1
  exact add_left_cancel h1
end VariableBound.Pairwise
