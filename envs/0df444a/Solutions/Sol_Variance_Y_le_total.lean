-- Prove2me | solution 1 for Variance.Y_le_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:43:48.719504+00:00
-- url     : https://prove2.me/submissions/107bd2b4-0beb-4c5f-b13d-ef9c893d3537

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Variance_Var
import Definitions.Def_Eight_ViaGrouping_Search
import Definitions.Def_Eight_SecNetworks_Grouping
import Definitions.Def_Eight_SecNetworks_Grouping
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_Variance_Grouping
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Variance_stYIsSum
import Theorems.Thm_Variance_sum_ordered_c
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Variance
open Finset Eight.SecNetworks Eight.ViaGrouping
namespace Variance
theorem _root_.solution {g K : ℕ} (c : Fin g → Fin g → ℕ) (χ : Fin g → Fin K) {γ γ' : Fin K} (hne : γ ≠ γ') : Y c χ γ γ' ≤ ∑ a, ∑ b ∈ univ.erase a, c a b := by
  rw [stYIsSum g K c χ γ γ' hne, ← sum_ordered_c]
  refine sum_le_sum fun p _ => ?_
  split_ifs
  · exact le_rfl
  · exact Nat.zero_le _
end Variance
