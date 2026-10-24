-- Prove2me | solution 1 for SurelyBetter.CLB.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:24:41.69729+00:00
-- url     : https://prove2.me/submissions/c859f21f-a703-4df6-b4b1-4b8c60abde9f

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_SurelyBetter_CLB_Model
import Theorems.Thm_SurelyBetter_CLB_theorem2_violation
import Theorems.Thm_SurelyBetter_CLB_theorem2_converse

open SurelyBetter.CLB

theorem solution {S : Type*} [Fintype S] (U : Set ℝ) (hU : Convex ℝ U)
    (hU2 : ∃ a ∈ U, ∃ b ∈ U, a ≠ b) (V : (S → ℝ) → ℝ) (ρ : Set S → ℝ)
    (hV : IsCLinBisep U V ρ) (E : Set S) :
    (ρ E + ρ Eᶜ < 1 → ¬ MOMOn V (measE U E)) ∧
    ((max (ρ E) (ρ Eᶜ) < 1 ∨ min (ρ E) (ρ Eᶜ) = 0) → 1 ≤ ρ E + ρ Eᶜ →
      MOMOn V (measE U E)) := by
  exact ⟨SurelyBetter.CLB.theorem2_violation U hU hU2 V ρ hV E,
    SurelyBetter.CLB.theorem2_converse U hU hU2 V ρ hV E⟩
