-- Prove2me | solution 1 for VariableBound.StepChoice.avgX
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:32:55.441858+00:00
-- url     : https://prove2.me/submissions/d8782b8b-4ae0-4b46-b119-264a9cf06231

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
import Theorems.Thm_VariableBound_StepChoice_allEven_nonneg
import Theorems.Thm_VariableBound_StepChoice_allEven_append
import Theorems.Thm_VariableBound_StepChoice_sum_ev_le

set_option autoImplicit false
section
section
open VariableBound VariableBound.StepChoice
open AppVariables Finset
variable {X E ι : Type} [Fintype X] [Fintype E] [DecidableEq E]
namespace VariableBound.StepChoice
theorem _root_.solution (V : X → Finset E) (nb : ℕ) (Ω : Finset ι) (Γ : ι → Finset E) (L : List (Finset E)) (hF : IsFamily nb Ω Γ) :
    4 * ∑ u ∈ Ω, Xsum V nb (L ++ [Γ u]) ≤ 3 * #Ω * Xsum V nb L := by
  calc 4 * ∑ u ∈ Ω, Xsum V nb (L ++ [Γ u])
      = ∑ ξ, ((#(V ξ)).choose (nb + 1) : ℤ) * allEven V L ξ * (4 * ∑ u ∈ Ω, ParityChecks.ev #(Γ u ∩ V ξ)) := by
        simp only [Xsum, allEven_append]
        rw [sum_comm, mul_sum]
        refine sum_congr rfl fun ξ _ => ?_
        rw [mul_sum, mul_sum, mul_sum]
        exact sum_congr rfl fun u _ => by ring
    _ ≤ ∑ ξ, ((#(V ξ)).choose (nb + 1) : ℤ) * allEven V L ξ * (3 * (#Ω : ℤ)) := by
        refine sum_le_sum fun ξ _ => ?_
        by_cases h : nb < #(V ξ)
        · exact mul_le_mul_of_nonneg_left (sum_ev_le hF _ h) (mul_nonneg (by positivity) (allEven_nonneg V L ξ))
        · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
    _ = 3 * #Ω * Xsum V nb L := by
        rw [Xsum, mul_sum]
        exact sum_congr rfl fun ξ _ => by ring
end VariableBound.StepChoice
