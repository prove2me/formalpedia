-- Prove2me | solution 1 for VariableBound.Net.Prof.length_objs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:49:39.959199+00:00
-- url     : https://prove2.me/submissions/6efec44c-e879-4c5e-9658-f04e61485297

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
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_VariableBound_Net_Basic_length_objs
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum



set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Prof
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F Finset
open PaddedDescent.F.Mark (Cl qv vio WfL occ nProf)
namespace VariableBound.Net.Prof
theorem _root_.solution {D : Dat} {s : ℕ} (hs : ∀ L ∈ D.2, L.length ≤ s) : (objs D).length ≤ D.2.length * s + D.1.length := by
  have h1 : (D.2.map List.length).sum ≤ (D.2.map List.length).length • s :=
    List.sum_le_card_nsmul _ _ fun x hx => by
      obtain ⟨L, hL, rfl⟩ := List.mem_map.1 hx
      exact hs L hL
  rw [List.length_map, smul_eq_mul] at h1
  rw [Basic.length_objs]
  omega
end VariableBound.Net.Prof
