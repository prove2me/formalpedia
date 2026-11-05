-- Prove2me | solution 1 for PaddedDescent.F.RebalF.mergedP_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:23:18.139882+00:00
-- url     : https://prove2.me/submissions/184af62c-ba53-4c97-8591-4c44436293d0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Table
import Definitions.Def_StepMachines_Prog_NetRun
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_PaddedDescent_F_RebalF
import Theorems.Thm_PaddedDescent_F_RebalF_mergedM_halts
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_NetE_mergedM_runs
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_Runs_unique
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.RebalF
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Stepped Finset
variable {C : Type}
namespace PaddedDescent.F.RebalF
theorem _root_.solution {K g : ℕ} {F : FNet C} {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {P B : ℕ}
    (hN : F.toP.Presents c N 0 0) (hS : N.Sized P B) (x β m : ℕ)
    (hm : ∀ G < K, (members K g x G).length ≤ m)
    (hβ : ∀ G < K, ∀ G' < K, G ≠ G' → lbLen K g F.toP c x G G' ≤ β)
    (G : Fin K) (θ : Fin K → List Bool) (hθ : ∀ G', G' ≠ G → (θ G').length = β) (hG : θ G = []) :
    mergedP K g F ((c, x), (G.val, List.ofFn θ)) = mergedVal K g F.toP N ((c, x), (G.val, List.ofFn θ)) := by
  let _ : HasSize C := ⟨fun _ => 0⟩
  obtain ⟨T, S, h⟩ := mergedM_halts K g F ((c, x), (G.val, List.ofFn θ))
  exact h.unique (mergedM_runs K g F.toP (hN.mono (Nat.zero_le 1) le_rfl) hS le_rfl x β m hm hβ G θ hθ hG)
end PaddedDescent.F.RebalF
