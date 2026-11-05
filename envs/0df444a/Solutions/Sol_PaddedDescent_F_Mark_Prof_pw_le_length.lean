-- Prove2me | solution 1 for PaddedDescent.F.Mark.Prof.pw_le_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:27:26.884347+00:00
-- url     : https://prove2.me/submissions/227e771a-4066-461f-aeaf-63747df72533

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
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Prof
open Groundwork Groundwork.Prog Groundwork.Grid Finset
namespace PaddedDescent.F.Mark.Prof
theorem _root_.solution (g n : ℕ) (Ls : List Fml) (P : Finset ℕ) (a b i : ℕ) : pw g n Ls P a b i ≤ (tst g n Ls a b i).length := by
  unfold pw
  calc (P.filter fun e => e ∈ tst g n Ls a b i).card ≤ (tst g n Ls a b i).toFinset.card :=
        card_le_card fun e he => List.mem_toFinset.2 (mem_filter.1 he).2
    _ ≤ _ := List.toFinset_card_le _
end PaddedDescent.F.Mark.Prof
