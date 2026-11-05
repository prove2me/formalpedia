-- Prove2me | solution 1 for VariableBound.SmallBias.card_pairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:25:51.183341+00:00
-- url     : https://prove2.me/submissions/7c5fec69-5fde-4130-b60a-60cedb5c7f4d

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
namespace VariableBound.SmallBias
theorem _root_.solution {A : Type} [Fintype A] (Q : A × A → Prop) [DecidablePred Q] : #{p : A × A | Q p} = ∑ a : A, #{b : A | Q (a, b)} := by
  simp only [card_filter]
  exact Fintype.sum_prod_type _
end VariableBound.SmallBias
