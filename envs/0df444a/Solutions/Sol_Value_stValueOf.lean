-- Prove2me | solution 1 for Value.stValueOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:58:29.929206+00:00
-- url     : https://prove2.me/submissions/4c8c9d6a-f68a-40f2-b6d0-f3ac3c84064c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Clique
import Definitions.Def_Value_Joint
import Definitions.Def_Value_End
import Theorems.Thm_Eight_SecNetworks_star_mem
import Theorems.Thm_Eight_ViaGrouping_groupedTables_eq_display
import Theorems.Thm_Groundwork_mem_tuples
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Paper_cliqueValue_def
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open Value
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Eight.SecNetworks Eight.ViaGrouping
namespace Value
theorem _root_.solution : StValueOf := by
  intro hC hV K g hK0 C _ Np c N P B τ S h x L hL
  rw [← hV C g K hK0 Np c N P B τ S h x L hL]
  unfold groupClique
  rw [hC K L (display Np c N hK0 x), Paper.cliqueValue_def]
  exact sum_congr rfl fun Λ hΛ => prod_congr rfl fun γ _ =>
    groupedTables_eq_display h hK0 x L hL γ _ fun γ' hne => mem_words.1 (((mem_tuples _ _ _ _).1 (star_mem hΛ γ) γ').1 hne)
end Value
