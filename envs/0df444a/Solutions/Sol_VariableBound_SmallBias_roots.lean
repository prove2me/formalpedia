-- Prove2me | solution 1 for VariableBound.SmallBias.roots
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:01:14.872408+00:00
-- url     : https://prove2.me/submissions/2ba1ae41-8627-4af6-aecb-b24eb25ff781

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
import Theorems.Thm_VariableBound_SmallBias_eval_poly
import Theorems.Thm_VariableBound_SmallBias_poly_ne_zero
import Theorems.Thm_VariableBound_SmallBias_poly_natDegree_le

set_option autoImplicit false
section
section
open VariableBound VariableBound.SmallBias
open Finset AppVariables
variable {F : Type} [Field F] {m : ℕ}
namespace VariableBound.SmallBias
theorem _root_.solution [Fintype F] [DecidableEq F] (V' : Finset (Fin m)) (hV : V'.Nonempty) : #{u₃ : F | ∑ E ∈ V', u₃ ^ E.val = 0} ≤ m - 1 := by
  refine le_trans (Polynomial.card_le_degree_of_subset_roots (p := poly F V') fun u hu => ?_) (poly_natDegree_le V')
  rw [Polynomial.mem_roots (poly_ne_zero V' hV), Polynomial.IsRoot, eval_poly]
  simpa using hu
end VariableBound.SmallBias
