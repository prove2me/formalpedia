-- Prove2me | solution 1 for VariableBound.StepChoice.avgUps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:33:36.70241+00:00
-- url     : https://prove2.me/submissions/d3471b87-6e17-4549-9180-c87e6d020453

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
import Theorems.Thm_VariableBound_StepChoice_avgX
import Theorems.Thm_VariableBound_StepChoice_pp_nonneg
import Theorems.Thm_VariableBound_StepChoice_avgCol
import Theorems.Thm_VariableBound_StepChoice_load_append

set_option autoImplicit false
section
section
open VariableBound VariableBound.StepChoice
open AppVariables Finset
variable {X E ι : Type} [Fintype X] [Fintype E] [DecidableEq E]
namespace VariableBound.StepChoice
theorem _root_.solution (V : X → Finset E) (nb β rb tb : ℕ) (Ω : Finset ι) (Γ : ι → Finset E) (L : List (Finset E)) (hnb : 1 ≤ nb) (hF : IsFamily nb Ω Γ)
    (hr : L.length < rb) : ∑ u ∈ Ω, Ups V nb β rb tb (L ++ [Γ u]) ≤ #Ω * Ups V nb β rb tb L := by
  have h1 : (4 : ℚ) * ∑ u ∈ Ω, (Xsum V nb (L ++ [Γ u]) : ℚ) ≤ 3 * #Ω * (Xsum V nb L : ℚ) := by exact_mod_cast avgX V nb Ω Γ L hF
  have h2 : ∀ e, ∑ u ∈ Ω, (2 : ℚ) ^ load (L ++ [Γ u]) e ≤ 2 ^ load L e * ((1 + pp nb) * #Ω) := by
    intro e
    simp only [load_append, pow_add]
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left (avgCol nb Ω Γ e hnb hF) (by positivity)
  have hp := pp_nonneg nb
  obtain ⟨d, hd⟩ : ∃ d, rb - L.length = d + 1 := ⟨rb - L.length - 1, by omega⟩
  have hd' : rb - (L.length + 1) = d := by omega
  unfold Ups
  simp only [List.length_append, List.length_singleton, hd, hd']
  rw [sum_add_distrib, ← sum_div, ← mul_sum, ← mul_sum, sum_comm, mul_add]
  refine add_le_add ?_ ?_
  · calc (4 / 3 : ℚ) ^ (L.length + 1) * (∑ u ∈ Ω, (Xsum V nb (L ++ [Γ u]) : ℚ)) / 2 ^ (β - 1)
        = (4 / 3 : ℚ) ^ L.length / 2 ^ (β - 1) * (4 * ∑ u ∈ Ω, (Xsum V nb (L ++ [Γ u]) : ℚ)) / 3 := by ring
      _ ≤ (4 / 3 : ℚ) ^ L.length / 2 ^ (β - 1) * (3 * #Ω * (Xsum V nb L : ℚ)) / 3 := by gcongr
      _ = #Ω * ((4 / 3 : ℚ) ^ L.length * (Xsum V nb L : ℚ) / 2 ^ (β - 1)) := by ring
  · calc (1 + pp nb) ^ d * (1 / 2 ^ tb) * ∑ e : E, ∑ u ∈ Ω, (2 : ℚ) ^ load (L ++ [Γ u]) e
        ≤ (1 + pp nb) ^ d * (1 / 2 ^ tb) * ∑ e : E, (2 : ℚ) ^ load L e * ((1 + pp nb) * #Ω) := by
          gcongr with e _
          exact h2 e
      _ = #Ω * ((1 + pp nb) ^ (d + 1) * (1 / 2 ^ tb) * ∑ e : E, (2 : ℚ) ^ load L e) := by
          rw [← sum_mul]; ring
end VariableBound.StepChoice
