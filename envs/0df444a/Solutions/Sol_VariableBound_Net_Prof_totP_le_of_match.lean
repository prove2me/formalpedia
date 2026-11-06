-- Prove2me | solution 1 for VariableBound.Net.Prof.totP_le_of_match
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:52:45.387311+00:00
-- url     : https://prove2.me/submissions/343c6d27-f4ec-405e-a4a8-ef1d7a0e520e

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
import Theorems.Thm_VariableBound_Net_Prof_totP_eq
import Theorems.Thm_VariableBound_Net_Prof_sum_pw_le
import Theorems.Thm_VariableBound_Net_Prof_tot_of_match
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_PaddedDescent_F_Mark_Prof_sum_pw_le
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Prof
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F Finset
open PaddedDescent.F.Mark (Cl qv vio WfL occ nProf)
namespace VariableBound.Net.Prof
theorem _root_.solution {k g n : ℕ} {D : Dat} (hg : 0 < g) (h : WfD k n D) {P : Finset ℕ} (hP : P ⊆ range (objs D).length) {y : ℕ}
    (hM : Match g n D y P) {κ : ℕ} (hκ : κ < 2) : totP g D y κ ≤ (k - 1 + κ) * tot g D y κ := by
  rw [tot_of_match hg h hP hM hκ, totP_eq, ← sum_congr rfl fun b hb => sum_congr rfl fun a ha =>
    (hM κ hκ a ((mem_range.1 ha).trans (mem_range.1 hb))).2 b (mem_range.1 hb) (by have := mem_range.1 ha; omega)]
  exact sum_pw_le hg h hP κ
end VariableBound.Net.Prof
