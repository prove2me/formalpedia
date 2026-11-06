-- Prove2me | solution 1 for VariableBound.Net.Prof.mu_le_of_match
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:30:06.174618+00:00
-- url     : https://prove2.me/submissions/50db8bf7-d2b1-477a-8aed-c233beea143f

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
import Theorems.Thm_VariableBound_Net_Prof_pw_le_length
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_PaddedDescent_F_Mark_Prof_pw_le_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Prof
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F Finset
open PaddedDescent.F.Mark (Cl qv vio WfL occ nProf)
namespace VariableBound.Net.Prof
theorem _root_.solution {g n : ℕ} {D : Dat} {P : Finset ℕ} {y : ℕ} (hM : Match g n D y P) {κ : ℕ} (hκ : κ < 2) {a b : ℕ} (ha : a < g) (hb : b < g)
    (hne : b ≠ a) : mu g D y a b κ ≤ (tst g n D a b κ).length := by
  rw [← (hM κ hκ a ha).2 b hb hne]
  exact pw_le_length _ _ _ _ _ _ _
end VariableBound.Net.Prof
