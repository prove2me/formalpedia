-- Prove2me | solution 1 for Variance.stSearchOfGrouping
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:08:18.921485+00:00
-- url     : https://prove2.me/submissions/cbe3f66d-bcec-40d7-9a6b-5b42be21d2fb

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
import Theorems.Thm_Eight_ViaGrouping_goodP_iff
import Theorems.Thm_Eight_ViaGrouping_grouping_number
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_P2M_Groundwork_PolyT_find__e812ffd764ea
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] P2M_Groundwork_PolyT_find__e812ffd764ea



set_option autoImplicit false
section
section
open Variance
open Finset Eight.SecNetworks Eight.ViaGrouping
namespace Variance
theorem _root_.solution : StSearchOfGrouping := by
  intro hG K hK C _ Np c N P B τ S h
  have hK0 : 0 < K := by omega
  obtain ⟨x', hx', hgood'⟩ : ∃ x < K ^ (3 * K ^ 8), goodP K (3 * K ^ 8) Np (c, x) = true := by
    obtain ⟨χ, hχ⟩ := hG.exists_good K P N.c hK h.is.c_symm h.is.i
    obtain ⟨x, hx, rfl⟩ := grouping_number hK0 χ
    exact ⟨x, hx, (goodP_iff hK0 h x).2 hχ⟩
  obtain ⟨x, hfind⟩ : ∃ x, (List.range (K ^ (3 * K ^ 8))).find? (fun x => goodP K (3 * K ^ 8) Np (c, x)) = some x := by
    rw [← Option.isSome_iff_exists, List.find?_isSome]
    exact ⟨x', List.mem_range.2 hx', hgood'⟩
  have hgood : goodP K (3 * K ^ 8) Np (c, x) = true := List.find?_some (p := fun x => goodP K (3 * K ^ 8) Np (c, x)) hfind
  exact ⟨x, List.mem_range.1 (List.mem_of_find?_eq_some hfind), hfind, (goodP_iff _ h x).1 hgood⟩
end Variance
