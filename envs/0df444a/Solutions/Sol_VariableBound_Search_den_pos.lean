-- Prove2me | solution 1 for VariableBound.Search.den_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:09:04.577954+00:00
-- url     : https://prove2.me/submissions/d4bc513e-c143-4d41-8e40-7fb2d1708f7a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Search_Defs
import Definitions.Def_VariableBound_StepChoice
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Search_Correct

set_option autoImplicit false
section
section
open VariableBound VariableBound.Search
open Groundwork PaddedDescent.F AppVariables Finset
namespace VariableBound.Search
theorem _root_.solution (nb β rb tb r : ℕ) (hnb : 1 ≤ nb) : 0 < den nb β rb tb r := by
  have : (0 : ℚ) < nb := by exact_mod_cast hnb
  unfold den; positivity
end VariableBound.Search
