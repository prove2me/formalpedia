-- Prove2me | solution 1 for VariableBound.StepChoice.reached_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:32:23.939877+00:00
-- url     : https://prove2.me/submissions/b7c0d065-e3e1-4cd6-a0fe-dec172cba2ee

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppVariablesStatement
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.List
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_StepChoice

set_option autoImplicit false
section
section
open VariableBound VariableBound.StepChoice
open AppVariables Finset
variable {X E ι : Type} [Fintype X] [Fintype E] [DecidableEq E]
namespace VariableBound.StepChoice
theorem _root_.solution (V : X → Finset E) (nb β rb tb : ℕ) (Ω : Finset ι) (Γ : ι → Finset E) (L : List (Finset E)) (hL : Reached V nb β rb tb Ω Γ L) :
    ∀ Λ ∈ L, ∃ u ∈ Ω, Λ = Γ u := by
  induction hL with
  | nil => intro Λ h; simp at h
  | step L u _ _ hu _ ih =>
    intro Λ h
    rcases List.mem_append.1 h with h | h
    · exact ih Λ h
    · exact ⟨u, hu, List.mem_singleton.1 h⟩
end VariableBound.StepChoice
