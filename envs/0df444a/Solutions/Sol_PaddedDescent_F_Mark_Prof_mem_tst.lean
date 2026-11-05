-- Prove2me | solution 1 for PaddedDescent.F.Mark.Prof.mem_tst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:38:27.131211+00:00
-- url     : https://prove2.me/submissions/9f1a709c-d502-4330-9516-927fcc3e03f5

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
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Prof
open Groundwork Groundwork.Prog Groundwork.Grid Finset
namespace PaddedDescent.F.Mark.Prof
theorem _root_.solution {g n : ℕ} {Ls : List Fml} {a' a i e : ℕ} (hlt : a' < a) :
    e ∈ tst g n Ls a' a i ↔ e < (cls Ls).length ∧ (clAt Ls e).1 = i ∧ linkB g n Ls e a' a = true := by
  unfold tst
  rw [List.mem_filter, List.mem_range, min_eq_left hlt.le, max_eq_right hlt.le, Bool.and_eq_true, beq_iff_eq]
end PaddedDescent.F.Mark.Prof
