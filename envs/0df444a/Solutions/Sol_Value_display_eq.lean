-- Prove2me | solution 1 for Value.display_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:32:09.816485+00:00
-- url     : https://prove2.me/submissions/01a32fde-7e7a-442a-b274-674385041366

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Blocks
import Definitions.Def_Value_Sums
import Definitions.Def_Value_Joint
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Value_thetaAt_eq_readBlocks


set_option autoImplicit false
section
section
open Value
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Eight.SecNetworks Eight.ViaGrouping
variable {C : Type} [HasSize C] {g K : ℕ}
namespace Value
theorem _root_.solution (hSB : StSameBlock) (Np : Procs C) (c : C) (N : Net g) (hK0 : 0 < K) (x : ℕ) {Λ : Fin K × Fin K → List Bool} (hA : AppendedZero g Np c x Λ) (γ : Fin K) :
    display Np c N hK0 x γ (star Λ γ) = ∑ z ∈ tuples (fun a => Paper.grouping hK0 x a = γ) N.S [], groupTerm N (Paper.grouping hK0 x) (readBlocks Np c hK0 x Λ) γ z := by
  unfold display
  rw [if_pos (hA γ), one_mul]
  refine sum_congr rfl fun z _ => ?_
  unfold groupTerm
  congr 1
  refine prod_congr rfl fun p hp => ?_
  obtain ⟨h1, h2⟩ := (mem_filter.1 hp).2
  rw [← thetaAt_eq_readBlocks hSB Np c hK0 x Λ (fun e => h2 (e ▸ h1)), h1]
end Value
