-- Prove2me | solution 1 for Value.stBlocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:47:57.795102+00:00
-- url     : https://prove2.me/submissions/e193ccf0-8a83-45a8-bcb2-691cd46c652a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Words
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_Value_Blocks
import Theorems.Thm_Value_stSameBlock
import Theorems.Thm_Value_readBlocks_mem
import Theorems.Thm_Value_length_blockString
import Theorems.Thm_Value_edge_unique
import Theorems.Thm_Value_blocks_iff
import Theorems.Thm_Eight_ViaGrouping_Table_lbLen_eq_Y
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Value_existsUnique_pi
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Value
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Eight.SecNetworks Eight.ViaGrouping
variable {C : Type} [HasSize C] {g K : ℕ}
variable {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
namespace Value
theorem _root_.solution : StBlocks := by
  intro C _ g K hK0 Np c N P B τ S h x L hL
  refine ⟨fun Λ hΛ _ => readBlocks_mem h hK0 x L hL hΛ, fun θ hθ => ?_⟩
  refine (existsUnique_congr fun Λ => blocks_iff stSameBlock Np c hK0 x L hθ Λ).2 (existsUnique_pi _ fun p => ?_)
  by_cases hp : p.1 < p.2
  · obtain ⟨w, hw, hu⟩ := edge_unique Np.toPaperNetwork hK0 c x L p.1 p.2 (by
      rw [Table.lbLen_eq_Y h hK0 x hp.ne]
      exact hL _ _ hp.ne) (fun q => θ (pr q.1 q.2)) fun q hq => length_blockString h hθ (by
        rw [hq.1, hq.2]
        exact hp.ne)
    exact ⟨w, ⟨fun _ => hw, fun hn => absurd hp hn⟩, fun w' hw' => hu w' (hw'.1 hp)⟩
  · exact ⟨[], ⟨fun h' => absurd h' hp, fun _ => rfl⟩, fun w' hw' => hw'.2 hp⟩
end Value
