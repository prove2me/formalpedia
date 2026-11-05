-- Prove2me | solution 1 for PaddedDescent.F.RebalF.stLen_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:14:03.097616+00:00
-- url     : https://prove2.me/submissions/ec257264-9505-4ac8-a244-11b3aff749aa

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Table
import Definitions.Def_StepMachines_Prog_NetRun
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_PaddedDescent_F_RebalF
import Theorems.Thm_PaddedDescent_F_RebalF_n_le
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_Prog_NetE_n_le
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.RebalF
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Stepped Finset
variable {C : Type}
namespace PaddedDescent.F.RebalF
theorem _root_.solution {F : FNet C} {c : C} {K g : ℕ} {N : Network (Fin g) (List Bool) (List Bool)} {P B : ℕ}
    (hN : F.toP.Presents c N 0 0) (hS : N.Sized P B) {x G m : ℕ} (hm : (members K g x G).length ≤ m) :
    stLen K g F.toP c x G ≤ P * m := by
  unfold stLen stLens
  have h1 := List.sum_le_card_nsmul ((members K g x G).map (F.toP.n c)) P (by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hy
    exact n_le hN hS ⟨a, List.mem_range.1 (List.mem_filter.1 ha).1⟩)
  rw [List.length_map, smul_eq_mul] at h1
  calc _ ≤ (members K g x G).length * P := h1
    _ ≤ m * P := Nat.mul_le_mul_right _ hm
    _ = P * m := Nat.mul_comm _ _
end PaddedDescent.F.RebalF
