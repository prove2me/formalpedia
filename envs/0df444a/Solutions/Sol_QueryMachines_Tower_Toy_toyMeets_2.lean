-- Prove2me | solution 2 for QueryMachines.Tower.Toy.toyMeets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:22:56.193026+00:00
-- url     : https://prove2.me/submissions/95994f3e-ade8-4bec-9bf9-b654be9daf53

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Tower_Toy_Defs
import Definitions.Def_Tower_Toy_Spec
import Definitions.Def_Tower_Kernel
import Definitions.Def_Tower_TowerRuns
import Definitions.Def_StepMachines_Prog_SideBasics
import Mathlib.Tactic.Ring
import Definitions.Def_Tower_Toy_Meets
import Theorems.Thm_QueryMachines_Tower_Toy_sol_within
import Theorems.Thm_QueryMachines_Tower_Toy_inn_within
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_size_bool
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_Groundwork_size_prod
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local simp] Groundwork.size_bool
attribute [local simp] Groundwork.size_nat
attribute [local simp] Groundwork.size_prod



set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Tower QueryMachines.Tower.Toy
open Groundwork Groundwork.Prog
namespace QueryMachines.Tower.Toy
theorem _root_.solution : ToyMeets := fun ℓ0 M0 => {
  child_lev := fun _ _ _ _ h => h
  child_good := fun c f c' hG h => by
    replace h : c'.1 + 1 = c.1 := h
    have hl : c.1 ≤ ℓ0 := hG.1
    refine ⟨(by omega : c'.1 ≤ ℓ0), fun q hq => ?_⟩
    replace hq : q.length = c'.1 := hq
    obtain ⟨a, ha, e⟩ := hG.2 (c'.2 :: q) (by rw [List.length_cons, hq]; exact h)
    exact ⟨a, ha, (if_pos hq).trans e⟩
  child_size := fun c f c' hG h => by
    replace h : c'.1 + 1 = c.1 := h
    have hl : c.1 ≤ ℓ0 := hG.1
    have := Nat.size_le_size (by omega : c'.1 ≤ ℓ0)
    rw [size_prod, size_nat, size_bool, SC]; omega
  sol := fun c f hG tc tq => sol_within ℓ0 M0 c f hG tc tq
  inn := fun c f c' hG hch q a ht tq => inn_within ℓ0 M0 c f c' hG hch q a ht tq }
end QueryMachines.Tower.Toy
