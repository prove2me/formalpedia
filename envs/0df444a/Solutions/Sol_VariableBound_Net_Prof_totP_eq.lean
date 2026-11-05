-- Prove2me | solution 1 for VariableBound.Net.Prof.totP_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:48:53.998631+00:00
-- url     : https://prove2.me/submissions/5c817549-86d9-4e2d-9c40-4ae7a781a9ab

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Basic
import Definitions.Def_StepMachines_Math_Digits
import Definitions.Def_PaddedDescent_F_MarkProf
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_VariableBound_Net_Prof
import Theorems.Thm_Groundwork_Stepped_sum_map_range
import Theorems.Thm_PaddedDescent_F_Mark_Prof_sum_map_range


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Prof
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F Finset
open PaddedDescent.F.Mark (Cl qv vio WfL occ nProf)
namespace VariableBound.Net.Prof
theorem _root_.solution (g : ℕ) (D : Dat) (y κ : ℕ) : totP g D y κ = ∑ b ∈ range g, ∑ a ∈ range b, mu g D y a b κ := by
  unfold totP
  rw [Mark.Prof.sum_map_range]
  exact sum_congr rfl fun b _ => Mark.Prof.sum_map_range _ _
end VariableBound.Net.Prof
