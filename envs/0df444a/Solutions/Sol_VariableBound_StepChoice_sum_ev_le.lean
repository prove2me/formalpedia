-- Prove2me | solution 1 for VariableBound.StepChoice.sum_ev_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:32:17.231478+00:00
-- url     : https://prove2.me/submissions/7cece1da-1cf1-425c-9cc1-9738c2985377

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
theorem _root_.solution {nb : ℕ} {Ω : Finset ι} {Γ : ι → Finset E} (hF : IsFamily nb Ω Γ) (W : Finset E) (hW : nb < #W) :
    4 * ∑ u ∈ Ω, ParityChecks.ev #(Γ u ∩ W) ≤ 3 * (#Ω : ℤ) := by
  have h1 : ∑ u ∈ Ω, ParityChecks.ev #(Γ u ∩ W) = (#{u ∈ Ω | Even #(Γ u ∩ W)} : ℤ) := by
    unfold ParityChecks.ev; rw [sum_boole]
  have h2 : #{u ∈ Ω | Even #(Γ u ∩ W)} + #{u ∈ Ω | Odd #(Γ u ∩ W)} = #Ω := by
    simp only [← Nat.not_even_iff_odd]
    exact card_filter_add_card_filter_not _
  have h3 := hF.c W hW
  rw [h1]
  have : 4 * #{u ∈ Ω | Even #(Γ u ∩ W)} ≤ 3 * #Ω := by omega
  exact_mod_cast this
end VariableBound.StepChoice
