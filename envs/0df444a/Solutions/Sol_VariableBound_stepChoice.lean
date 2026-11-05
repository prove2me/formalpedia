-- Prove2me | solution 1 for VariableBound.stepChoice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:53:16.170065+00:00
-- url     : https://prove2.me/submissions/da481db7-275c-4418-a8b2-66ed08e579d8

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
import Theorems.Thm_VariableBound_StepChoice_Xsum_nonneg
import Theorems.Thm_VariableBound_StepChoice_avgX
import Theorems.Thm_VariableBound_StepChoice_avgCol
import Theorems.Thm_VariableBound_StepChoice_load_append
import Theorems.Thm_VariableBound_StepChoice_avgUps
import Theorems.Thm_VariableBound_StepChoice_x_of_ups
import Theorems.Thm_VariableBound_StepChoice_lt_rb
import Theorems.Thm_VariableBound_StepChoice_load_of_ups
import Theorems.Thm_VariableBound_StepChoice_one_le_beta
import Theorems.Thm_VariableBound_StepChoice_reached
import Theorems.Thm_VariableBound_StepChoice_reached_mem
import Theorems.Thm_VariableBound_StepChoice_progress

set_option autoImplicit false
section
section
open VariableBound
open AppVariables Finset
namespace VariableBound
theorem _root_.solution : AppVariables.StepChoice where
  avgX := fun _ _ _ _ _ _ V nb Ω Γ L hF => StepChoice.avgX V nb Ω Γ L hF
  avgCol := fun _ _ _ _ nb Ω Γ e hnb hF => StepChoice.avgCol nb Ω Γ e hnb hF
  avgUps := fun _ _ _ _ _ _ V nb β rb tb Ω Γ L hnb hF hr => StepChoice.avgUps V nb β rb tb Ω Γ L hnb hF hr
  ups_le := fun _ _ _ _ _ _ V n nb rb tb Ω Γ L hX hnb hrb htb hF hL => StepChoice.reached V n nb rb tb Ω Γ L hX hnb hrb htb hF hL
  x_le := fun _ _ _ _ _ _ V n nb rb tb Ω Γ L hX hnb hrb htb hF hL =>
    StepChoice.x_of_ups V nb _ rb tb L (StepChoice.one_le_beta _ _ _) (StepChoice.reached V n nb rb tb Ω Γ L hX hnb hrb htb hF hL).2
  progress := fun _ _ _ _ _ _ V nb β rb tb Ω Γ L hΩ hL hpos => StepChoice.progress V nb β rb tb Ω Γ L hΩ hL hpos
  ends := by
    intro X E ι _ _ _ V n nb rb tb Ω Γ L hX hnb hrb htb hF hL hlen
    have h := StepChoice.reached V n nb rb tb Ω Γ L hX hnb hrb htb hF hL
    by_contra hne
    have hpos : 0 < Xsum V nb L := lt_of_le_of_ne (StepChoice.Xsum_nonneg V nb L) (Ne.symm hne)
    have := StepChoice.lt_rb V nb _ rb L hrb.1 h.1 hpos (StepChoice.x_of_ups V nb _ rb tb L (StepChoice.one_le_beta _ _ _) h.2)
    omega
  structure_ := by
    intro X E ι _ _ _ V n nb rb tb Ω Γ L L' hX hnb hrb htb hF hL hL'
    have h := StepChoice.reached V n nb rb tb Ω Γ L hX hnb hrb htb hF hL
    have hm := StepChoice.reached_mem V nb _ rb tb Ω Γ L hL
    have hc := StepChoice.load_of_ups V nb _ rb tb L h.2
    have ha : ∀ Λ ∈ L, nb * #Λ ≤ 16 * Fintype.card E := by
      intro Λ hΛ
      obtain ⟨u, hu, rfl⟩ := hm Λ hΛ
      exact hF.a u hu
    rcases hL' with rfl | ⟨hpos, u, hu, rfl⟩
    · exact ⟨h.1, ha, fun e => (hc e).trans (by omega)⟩
    · have hlt := StepChoice.lt_rb V nb _ rb L hrb.1 h.1 hpos (StepChoice.x_of_ups V nb _ rb tb L (StepChoice.one_le_beta _ _ _) h.2)
      refine ⟨by rw [List.length_append, List.length_singleton]; omega, ?_, ?_⟩
      · intro Λ hΛ
        rcases List.mem_append.1 hΛ with hΛ | hΛ
        · exact ha Λ hΛ
        · rw [List.mem_singleton.1 hΛ]; exact hF.a u hu
      · intro e
        rw [StepChoice.load_append]
        have := hc e
        split <;> omega
end VariableBound
