-- Prove2me | solution 1 for QueryMachines.Tower.Toy.toyRuns
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T00:27:58.533584+00:00
-- url     : https://prove2.me/submissions/ab554723-911c-41f1-a2b9-31cd8dc7da0e

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
import Theorems.Thm_QueryMachines_Tower_towerRuns
set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Tower QueryMachines.Tower.Toy
open Groundwork Groundwork.Prog

namespace QueryMachines.Tower.Toy

private theorem sumF_eq_aux : ∀ (l : ℕ) (f : List Bool → Option ℕ),
    sumF l f = ((words l).map fun q => (f q).getD 0).sum
  | 0, f => by simp [sumF, words]
  | l + 1, f => by simp [sumF, words, sumF_eq_aux l, List.map_map, Function.comp_def]

private theorem cost_toy_aux : ∀ l t : ℕ, cost TS TI l t + 5 = 2 ^ l * (t + 2 * l + 5)
  | 0, t => by show t + 5 = _; ring
  | l + 1, t => by
    have ih := cost_toy_aux l (t + 2)
    have e : 2 ^ (l + 1) * (t + 2 * (l + 1) + 5) =
        2 * (2 ^ l * (t + 2 + 2 * l + 5)) := by ring
    rw [e, ← ih]
    show 2 * (cost TS TI l (t + 2) + 2) + 1 + 5 = _
    omega

end QueryMachines.Tower.Toy

theorem solution : ToyRuns := by
  intro ℓ M0 t b f hf
  obtain ⟨own, L, hr, hc⟩ := towerRuns _ _ _ _ (spec ℓ M0) noG noW Sol Inn TS TI _ _ _
    (toyMeets ℓ M0) (ℓ, b) f ⟨le_rfl, hf⟩ t
  rw [← sumF_eq_aux]
  have := cost_toy_aux ℓ t
  exact ⟨own, L, hr, hc.trans (by show cost TS TI ℓ t ≤ _; omega)⟩
