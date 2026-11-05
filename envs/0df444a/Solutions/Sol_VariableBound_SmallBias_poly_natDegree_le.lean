-- Prove2me | solution 1 for VariableBound.SmallBias.poly_natDegree_le
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:45:44.138199+00:00
-- url     : https://prove2.me/submissions/089d45a0-08e1-4fa4-ba15-b0fd3f957a00

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

theorem solution (V' : Finset (Fin m)) : (poly F V').natDegree ≤ m - 1 := by
  classical
  unfold VariableBound.SmallBias.poly
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro E _
  rw [Polynomial.natDegree_X_pow]
  exact Nat.le_sub_one_of_lt E.isLt
