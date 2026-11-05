-- Prove2me | solution 1 for VariableBound.SmallBias.eval_poly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:57:41.459997+00:00
-- url     : https://prove2.me/submissions/387a1f88-7380-487e-9267-0c44872f90a1

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
theorem _root_.solution (V' : Finset (Fin m)) (u₃ : F) : (poly F V').eval u₃ = ∑ E ∈ V', u₃ ^ E.val := by
  simp [poly, Polynomial.eval_finsetSum]
end VariableBound.SmallBias
