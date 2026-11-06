-- Prove2me | solution 1 for Value.edge_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:31:57.723405+00:00
-- url     : https://prove2.me/submissions/efa3b498-3362-49ab-b25a-ded302a2335f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Words
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_Value_Blocks
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_NetE_sum_mdec
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Value_existsUnique_of_sum
import Theorems.Thm_Value_existsUnique_tuple
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open Value
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Eight.SecNetworks Eight.ViaGrouping
variable {C : Type} [HasSize C] {g K : ℕ}
variable {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
omit [HasSize C]
namespace Value
theorem _root_.solution (Nq : PNet C) (hK0 : 0 < K) (c : C) (x L : ℕ) (G G' : Fin K) (hle : lbLen K g Nq c x G G' ≤ L) (t : Fin g × Fin g → List Bool)
    (ht : ∀ q : Fin g × Fin g, Paper.grouping hK0 x q.1 = G ∧ Paper.grouping hK0 x q.2 = G' → (t q).length = Nq.cap c q.1 q.2) :
    ∃! w : List Bool, w ∈ mD K g Nq c x L G G' ∧ ∀ q : Fin g × Fin g, Paper.grouping hK0 x q.1 = G ∧ Paper.grouping hK0 x q.2 = G' → mdec K g Nq c x G G' w q = t q :=
  existsUnique_of_sum _ _ _ (sum_mdec Nq hK0 c x L G G' hle) (fun t' => ∀ q : Fin g × Fin g, Paper.grouping hK0 x q.1 = G ∧ Paper.grouping hK0 x q.2 = G' → t' q = t q)
    (existsUnique_tuple _ _ _ t fun q hq => mem_words.2 (ht q hq))
end Value
