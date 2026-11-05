-- Prove2me | solution 1 for PaddedDescent.F.Mark.Prof.stProfSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T03:31:48.541753+00:00
-- url     : https://prove2.me/submissions/50db24c1-b6ae-4de6-a893-6c034919d924

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_StepMachines_Math_Digits
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_PaddedDescent_F_MarkProf
import Theorems.Thm_PaddedDescent_F_Mark_Prof_sum_digit_eq
import Theorems.Thm_PaddedDescent_F_Mark_Prof_tgt_le
import Theorems.Thm_PaddedDescent_F_Mark_Prof_adm_match_iff
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Prof
open Groundwork Groundwork.Prog Groundwork.Grid Finset
namespace PaddedDescent.F.Mark.Prof
theorem _root_.solution : StProfSum := by
  classical
  intro k g n w Ls P hg h hP
  have key := adm_match_iff w hg h hP
  by_cases hc : ∀ i < Ls.length, (layP Ls P i).card ≤ w
  · rw [if_pos hc]
    calc _ = ∑ y ∈ range (((cls Ls).length + 1) ^ (g * g * Ls.length)),
          (if ∀ q < g * g * Ls.length, digit (cls Ls).length y q = tgt g n Ls P q then (1 : ℤ) else 0) :=
          sum_congr rfl fun y _ => if_congr (by rw [key y]; exact and_iff_right hc) rfl rfl
      _ = _ := by rw [sum_digit_eq, if_pos fun q _ => tgt_le hP q]
  · rw [if_neg hc]
    exact sum_eq_zero fun y _ => if_neg (by rw [key y]; exact fun hh => hc hh.1)
end PaddedDescent.F.Mark.Prof
