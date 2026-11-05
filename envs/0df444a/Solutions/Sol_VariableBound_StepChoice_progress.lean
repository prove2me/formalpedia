-- Prove2me | solution 1 for VariableBound.StepChoice.progress
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:52:20.904547+00:00
-- url     : https://prove2.me/submissions/fe292398-a9e3-4519-8a57-3db1ad6726e0

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
theorem _root_.solution (V : X → Finset E) (nb β rb tb : ℕ) (Ω : Finset ι) (Γ : ι → Finset E) (L : List (Finset E)) (hΩ : Ω.Nonempty)
    (hL : Reached V nb β rb tb Ω Γ L) (hpos : 0 < Xsum V nb L) : ∃ u ∈ Ω, Reached V nb β rb tb Ω Γ (L ++ [Γ u]) := by
  obtain ⟨u, hu, hmin⟩ := exists_min_image Ω (fun u => Ups V nb β rb tb (L ++ [Γ u])) hΩ
  exact ⟨u, hu, Reached.step L u hL hpos hu hmin⟩
end VariableBound.StepChoice
