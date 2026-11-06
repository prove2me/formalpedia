-- Prove2me | solution 1 for VariableBound.Net.Prof.stProf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:08:19.245647+00:00
-- url     : https://prove2.me/submissions/1e657c7c-02e6-4a72-a232-8250e7a10e90

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
import Theorems.Thm_VariableBound_Net_Prof_tgt_le
import Theorems.Thm_VariableBound_Net_Prof_adm_match_iff
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_key
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_PaddedDescent_F_Mark_Prof_adm_match_iff
import Theorems.Thm_PaddedDescent_F_Mark_Prof_sum_digit_eq
import Theorems.Thm_PaddedDescent_F_Mark_Prof_tgt_le
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Prof
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F Finset
open PaddedDescent.F.Mark (Cl qv vio WfL occ nProf)
namespace VariableBound.Net.Prof
theorem _root_.solution : StProf := by
  classical
  intro k g n nb M D fl P hg h hP
  have key := adm_match_iff nb M fl hg h hP
  by_cases hc : Lim nb M D fl P
  · rw [if_pos hc]
    calc _ = ∑ y ∈ range (((objs D).length + 1) ^ (g * g * 2)),
          (if ∀ q < g * g * 2, digit (objs D).length y q = tgt g n D P q then (1 : ℤ) else 0) :=
          sum_congr rfl fun y _ => if_congr (by rw [key y]; exact and_iff_right hc) rfl rfl
      _ = _ := by rw [Mark.Prof.sum_digit_eq, if_pos fun q _ => tgt_le hP q]
  · rw [if_neg hc]
    exact sum_eq_zero fun y _ => if_neg (by rw [key y]; exact fun hh => hc hh.1)
end VariableBound.Net.Prof
