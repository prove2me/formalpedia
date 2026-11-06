-- Prove2me | solution 2 for QueryMachines.Tower.Toy.toyRuns
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:26:27.672198+00:00
-- url     : https://prove2.me/submissions/46f49a25-62ff-4c2d-bf52-6583bff21c0b

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
import Theorems.Thm_QueryMachines_Tower_Toy_toyMeets
import Theorems.Thm_QueryMachines_Tower_Toy_cost_toy
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_QueryMachines_Tower_Toy_sumF_eq
import Theorems.Thm_QueryMachines_Tower_towerRuns


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Tower QueryMachines.Tower.Toy
open Groundwork Groundwork.Prog
namespace QueryMachines.Tower.Toy
theorem _root_.solution : ToyRuns := by
  intro ℓ M0 t b f hf
  obtain ⟨own, L, hr, hc⟩ := towerRuns _ _ _ _ (spec ℓ M0) noG noW Sol Inn TS TI _ _ _ (toyMeets ℓ M0) (ℓ, b) f ⟨le_rfl, hf⟩ t
  rw [← sumF_eq]
  have := cost_toy ℓ t
  exact ⟨own, L, hr, hc.trans (by show cost TS TI ℓ t ≤ _; omega)⟩
end QueryMachines.Tower.Toy
