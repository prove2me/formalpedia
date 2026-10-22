-- Prove2me | solution 1 for RoundRobinEq.SubmodularBluff.tight_bluff_run
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:10:10.914611+00:00
-- url     : https://prove2.me/submissions/7f602a9f-31fc-49e4-8be8-83c19739e0a9

import Mathlib
import Definitions.Def_RoundRobinEq_SubmodularBluff_Setting
import Definitions.Def_RoundRobinEq_SubmodularBluff_Bluff
import Definitions.Def_RoundRobinEq_SubmodularBluff_TightInstance

set_option autoImplicit false
open RoundRobinEq.SubmodularBluff

theorem solution (ε₁ ε₂ ε₃ : ℝ) (h₁ : 0 < ε₁) (h₁₂ : ε₁ < ε₂) (h₂₃ : ε₂ < ε₃)
    (h₃ : ε₃ < 1) :
    IsGreedyOrder (tightVal ε₁ ε₂ ε₃) tightBluffOrder ∧
      RoundRobinEq.CancelableBluff.roundRobin (bluff tightBluffOrder : Fin 2 → List (Fin 6)) 0 = {0, 2, 4} ∧
      RoundRobinEq.CancelableBluff.roundRobin (bluff tightBluffOrder : Fin 2 → List (Fin 6)) 1 = {1, 3, 5} ∧
      tightVal ε₁ ε₂ ε₃ 0 {0, 2, 4} = 4 - ε₁ - ε₃ ∧
      tightVal ε₁ ε₂ ε₃ 1 {1, 3, 5} = 1 := by
  have hb : ∀ j : Fin 6, greedyBundle 2 tightBluffOrder j =
      ![(∅ : Finset (Fin 6)), ∅, {0}, {1}, {0, 2}, {1, 3}] j := by decide
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · unfold RoundRobinEq.CancelableBluff.IsRanking tightBluffOrder
    decide
  · intro j hj g hg
    have hj6 : j < 6 := by simpa [tightBluffOrder] using hj
    have hbj := hb ⟨j, hj6⟩
    rw [hbj]
    have hag : RoundRobinEq.CancelableBluff.agentAt 2 j = if j % 2 = 0 then 0 else 1 := by
      unfold RoundRobinEq.CancelableBluff.agentAt
      ext
      by_cases h : j % 2 = 0 <;> simp [h] <;> omega
    interval_cases j <;> fin_cases g <;>
      simp [tightBluffOrder, RoundRobinEq.CancelableBluff.marginal, tightVal, hag] at hg ⊢ <;>
      first | linarith | (left; linarith)
  · decide
  · decide
  · simp [tightVal]; ring
  · simp [tightVal]
    linarith
