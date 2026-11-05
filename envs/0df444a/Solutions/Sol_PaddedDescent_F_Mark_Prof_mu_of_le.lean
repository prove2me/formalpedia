-- Prove2me | solution 1 for PaddedDescent.F.Mark.Prof.mu_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:23:07.155835+00:00
-- url     : https://prove2.me/submissions/5de3e9c4-9a54-47f1-83bf-686573e155dd

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
theorem _root_.solution (g : ℕ) (Ls : List Fml) (y : ℕ) {a b : ℕ} (h : a ≤ b) (i : ℕ) :
    mu g Ls y a b i = digit (cls Ls).length y ((a * g + b) * Ls.length + i) := by
  unfold mu; rw [min_eq_left h, max_eq_right h]
end PaddedDescent.F.Mark.Prof
