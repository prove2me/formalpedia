-- Prove2me | solution 1 for QueryMachines.QueryMachine.stepped_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:48:32.807182+00:00
-- url     : https://prove2.me/submissions/f9892626-17aa-409a-a54b-83b601f25909

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_Kernel
import Definitions.Def_StepMachines_Prog_Stepped
import Mathlib.Tactic
import Definitions.Def_QueryMachines_Runs

set_option autoImplicit false
section
section
open QueryMachines QueryMachines.QueryMachine
open Groundwork
variable {Q A Q' A' C α β : Type}
namespace QueryMachines.QueryMachine
theorem _root_.solution {σ : Type} [HasSize σ] {i i' : α → σ} {st st' : σ → σ} {o o' : σ → Option β} (h1 : ∀ a, i a = i' a)
    (h2 : ∀ s, st s = st' s) (h3 : ∀ s, o s = o' s) : (⟨σ, i, st, o⟩ : Stepped α β) = ⟨σ, i', st', o'⟩ := by
  obtain rfl : i = i' := funext h1
  obtain rfl : st = st' := funext h2
  obtain rfl : o = o' := funext h3
  rfl
end QueryMachines.QueryMachine
