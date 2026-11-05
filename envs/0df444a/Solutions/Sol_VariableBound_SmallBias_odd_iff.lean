-- Prove2me | solution 1 for VariableBound.SmallBias.odd_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:56:57.790199+00:00
-- url     : https://prove2.me/submissions/f2d680d0-d186-45e3-b178-6113fa92ced1

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
theorem _root_.solution {ι : Type} (T : Finset ι) (f : ι → ZMod 2) : Odd #{e ∈ T | f e = 1} ↔ ∑ e ∈ T, f e = 1 := by
  have h : ∀ c : ZMod 2, c = if c = 1 then 1 else 0 := by decide
  rw [← ZMod.natCast_eq_one_iff_odd, natCast_card_filter]
  rw [sum_congr rfl fun e _ => h (f e)]
end VariableBound.SmallBias
