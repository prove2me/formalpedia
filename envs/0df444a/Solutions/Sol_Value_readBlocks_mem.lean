-- Prove2me | solution 1 for Value.readBlocks_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:30:09.552088+00:00
-- url     : https://prove2.me/submissions/f9e25532-59bc-486c-b075-1756240d6ac9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Words
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_Value_Blocks
import Theorems.Thm_Eight_SecNetworks_length_thetaAt
import Theorems.Thm_Eight_SecNetworks_star_mem
import Theorems.Thm_Eight_ViaGrouping_Table_isPaperNetwork
import Theorems.Thm_Groundwork_Network_merge_c
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_mem_tuples
import Theorems.Thm_Groundwork_mem_words
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
namespace Value
theorem _root_.solution (h : IsNetworkP Np c N P B τ S) (hK0 : 0 < K) (x L : ℕ) (hL : ∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L)
    {Λ : Fin K × Fin K → List Bool} (hΛ : Λ ∈ edgeStrings K L) : readBlocks Np c hK0 x Λ ∈ blockStrings N (Paper.grouping hK0 x) := by
  refine (mem_tuples _ _ _ _).2 fun p => ⟨fun hp => ?_, fun hp => if_neg hp⟩
  have hlen := length_thetaAt Np.toPaperNetwork hK0 (Table.isPaperNetwork h) x L (fun γ γ' hne => by
    rw [Groundwork.Network.merge_c]
    exact hL γ γ' hne) (star Λ (Paper.grouping hK0 x p.1)) hp.2 (mem_words.1 (((mem_tuples _ _ _ _).1 (star_mem hΛ _) _).1 hp.2.symm))
  rw [mem_words]
  exact (congrArg List.length (if_pos hp)).trans hlen
end Value
