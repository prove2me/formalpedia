-- Prove2me | solution 1 for VariableBound.Net.Prof.pw_le_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:49:06.196373+00:00
-- url     : https://prove2.me/submissions/5129b9f2-aeff-4a79-8a68-ce684f1165df

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
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Prof
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F Finset
open PaddedDescent.F.Mark (Cl qv vio WfL occ nProf)
namespace VariableBound.Net.Prof
theorem _root_.solution (g n : ℕ) (D : Dat) (P : Finset ℕ) (a b κ : ℕ) : pw g n D P a b κ ≤ (tst g n D a b κ).length := by
  unfold pw
  calc (P.filter fun o => o ∈ tst g n D a b κ).card ≤ (tst g n D a b κ).toFinset.card :=
        card_le_card fun o ho => List.mem_toFinset.2 (mem_filter.1 ho).2
    _ ≤ _ := List.toFinset_card_le _
end VariableBound.Net.Prof
