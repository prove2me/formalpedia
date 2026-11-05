-- Prove2me | solution 1 for QueryMachines.QueryMachine.Reaches.unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:02:37.128777+00:00
-- url     : https://prove2.me/submissions/9761144f-59a4-4e5e-bffc-0b888ff5fb6b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_Kernel
import Definitions.Def_StepMachines_Prog_Stepped
import Mathlib.Tactic
import Definitions.Def_QueryMachines_Runs
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.QueryMachine
open Groundwork
variable {Q A Q' A' C α β : Type}
namespace QueryMachines.QueryMachine
namespace Reaches
theorem _root_.solution {M : QueryMachine Q A α β} {O : Q → Option A} {S S' own own' : ℕ} {L L' : List Q} {b b' : β} {s : M.σ}
    (h : M.Reaches O S b s own L) (h' : M.Reaches O S' b' s own' L') : b = b' ∧ L = L' := by
  induction h generalizing own' L' with
  | halt h1 _ =>
    cases h' with
    | halt g1 _ => exact ⟨Option.some.inj (h1.symm.trans g1), rfl⟩
    | step g1 _ _ _ => rw [h1] at g1; cases g1
    | query g1 _ _ _ _ => rw [h1] at g1; cases g1
  | step h1 h2 _ _ ih =>
    cases h' with
    | halt g1 _ => rw [h1] at g1; cases g1
    | step _ _ _ g => exact ih g
    | query _ g2 _ _ _ => rw [h2] at g2; cases g2
  | query h1 h2 h3 _ _ ih =>
    cases h' with
    | halt g1 _ => rw [h1] at g1; cases g1
    | step _ g2 _ _ => rw [h2] at g2; cases g2
    | query _ g2 g3 _ g =>
      obtain rfl := Option.some.inj (h2.symm.trans g2)
      obtain rfl := Option.some.inj (h3.symm.trans g3)
      obtain ⟨hb, hL⟩ := ih g
      exact ⟨hb, by rw [hL]⟩
end Reaches
end QueryMachines.QueryMachine
