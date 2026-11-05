-- Prove2me | solution 1 for VariableBound.StepChoice.reached
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:52:04.274346+00:00
-- url     : https://prove2.me/submissions/f1e66fc9-a3b9-41bc-9b08-70ed189db0e8

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
import Theorems.Thm_VariableBound_StepChoice_minUps
import Theorems.Thm_VariableBound_StepChoice_ups_nil
import Theorems.Thm_VariableBound_StepChoice_x_of_ups
import Theorems.Thm_VariableBound_StepChoice_lt_rb
import Theorems.Thm_VariableBound_StepChoice_one_le_beta

set_option autoImplicit false
section
section
open VariableBound VariableBound.StepChoice
open AppVariables Finset
variable {X E ι : Type} [Fintype X] [Fintype E] [DecidableEq E]
namespace VariableBound.StepChoice
theorem _root_.solution (V : X → Finset E) (n nb rb tb : ℕ) (Ω : Finset ι) (Γ : ι → Finset E) (L : List (Finset E)) (hX : Fintype.card X ≤ 2 ^ n) (hnb : 1 ≤ nb)
    (hrb : IsRb (beta n (Fintype.card E) nb) rb) (htb : IsTb (Fintype.card E) nb rb tb) (hF : IsFamily nb Ω Γ)
    (hL : Reached V nb (beta n (Fintype.card E) nb) rb tb Ω Γ L) : L.length ≤ rb ∧ Ups V nb (beta n (Fintype.card E) nb) rb tb L ≤ 2 := by
  induction hL with
  | nil => exact ⟨Nat.zero_le _, ups_nil V n nb rb tb hX htb.1⟩
  | step L u _ hpos hu hmin ih =>
    have hlt := lt_rb V nb _ rb L hrb.1 ih.1 hpos (x_of_ups V nb _ rb tb L (one_le_beta _ _ _) ih.2)
    refine ⟨by rw [List.length_append, List.length_singleton]; omega, ?_⟩
    exact (minUps V nb _ rb tb Ω Γ L hnb hF hlt u hu hmin).trans ih.2
end VariableBound.StepChoice
