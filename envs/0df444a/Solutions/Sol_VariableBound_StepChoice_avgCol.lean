-- Prove2me | solution 1 for VariableBound.StepChoice.avgCol
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:26:22.431021+00:00
-- url     : https://prove2.me/submissions/709a60fa-d5a5-4487-9406-c463f46523d8

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
theorem _root_.solution (nb : ℕ) (Ω : Finset ι) (Γ : ι → Finset E) (e : E) (hnb : 1 ≤ nb) (hF : IsFamily nb Ω Γ) :
    ∑ u ∈ Ω, (2 : ℚ) ^ (if e ∈ Γ u then 1 else 0) ≤ (1 + pp nb) * #Ω := by
  have h1 : ∑ u ∈ Ω, (2 : ℚ) ^ (if e ∈ Γ u then 1 else 0) = #Ω + #{u ∈ Ω | e ∈ Γ u} := by
    rw [← sum_boole, card_eq_sum_ones, Nat.cast_sum, ← sum_add_distrib]
    refine sum_congr rfl fun u _ => ?_
    split <;> norm_num
  have h2 : (15 : ℚ) * nb * #{u ∈ Ω | e ∈ Γ u} ≤ 16 * #Ω := by exact_mod_cast hF.b e
  have h3 : (0 : ℚ) < 15 * nb := by
    have : (0 : ℚ) < nb := by exact_mod_cast hnb
    positivity
  have h4 : (#{u ∈ Ω | e ∈ Γ u} : ℚ) ≤ pp nb * #Ω := by
    unfold pp
    rw [div_mul_eq_mul_div, le_div_iff₀ h3]
    linarith
  rw [h1]; linarith
end VariableBound.StepChoice
