-- Prove2me | solution 1 for VariableBound.Search.sum_load
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:59:21.571409+00:00
-- url     : https://prove2.me/submissions/2d10fbbd-9e62-4e4d-8296-2a95b81c4041

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
import Theorems.Thm_VariableBound_Search_load_chksD
import Theorems.Thm_VariableBound_Search_sum_map_range

set_option autoImplicit false
section
section
open VariableBound VariableBound.Search
open Groundwork PaddedDescent.F AppVariables Finset
namespace VariableBound.Search
theorem _root_.solution (m : ℕ) (L : List (List ℕ)) : ∑ e : Fin m, (2 : ℚ) ^ load (chksD m L) e = (loadSum m L : ℚ) := by
  unfold loadSum
  rw [sum_map_range]
  push_cast
  exact sum_congr rfl fun e _ => by rw [load_chksD]
end VariableBound.Search
