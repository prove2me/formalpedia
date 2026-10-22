-- Prove2me | solution 1 for RoundRobinEq.SubmodularBluff.tight_deviation
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:13:01.829989+00:00
-- url     : https://prove2.me/submissions/adb3a68e-229b-44b7-b32f-6a0c3e888eb6

import Mathlib
import Definitions.Def_RoundRobinEq_SubmodularBluff_Setting
import Definitions.Def_RoundRobinEq_SubmodularBluff_Bluff
import Definitions.Def_RoundRobinEq_SubmodularBluff_TightInstance

set_option autoImplicit false
open RoundRobinEq.SubmodularBluff

theorem solution (ε₁ ε₂ ε₃ : ℝ) (h₁ : 0 < ε₁) (h₁₂ : ε₁ < ε₂) (h₂₃ : ε₂ < ε₃)
    (h₃ : ε₃ ≤ 1 / 2) :
    (∀ τ : List (Fin 6), RoundRobinEq.CancelableBluff.IsRanking τ →
      tightVal ε₁ ε₂ ε₃ 1 (RoundRobinEq.CancelableBluff.roundRobin (Function.update (bluff tightBluffOrder : Fin 2 → List (Fin 6)) 1 τ) 1) ≤ 2 - ε₁ - ε₂) ∧
    RoundRobinEq.CancelableBluff.IsRanking tightDeviation ∧
      RoundRobinEq.CancelableBluff.roundRobin (Function.update (bluff tightBluffOrder : Fin 2 → List (Fin 6)) 1 tightDeviation) 1 = {2, 3, 5} ∧
      tightVal ε₁ ε₂ ε₃ 1 {2, 3, 5} = 2 - ε₁ - ε₂ := by
  have hreach : ∀ a b c d e f : Fin 6, [a, b, c, d, e, f].Nodup →
      RoundRobinEq.CancelableBluff.roundRobin
        (Function.update (bluff tightBluffOrder : Fin 2 → List (Fin 6)) 1 [a, b, c, d, e, f]) 1 ∈
        ([{1, 3, 5}, {1, 4, 5}, {2, 3, 5}, {2, 4, 5}, {3, 4, 5}] : List (Finset (Fin 6))) := by
    decide +kernel
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro τ hτ
    obtain ⟨hnd, hall⟩ := hτ
    have hl : τ.length = 6 := by
      have : τ.toFinset = Finset.univ := by
        ext g; simp [hall]
      have h2 := List.toFinset_card_of_nodup hnd
      rw [this] at h2
      simpa using h2.symm
    match τ, hl, hnd with
    | [a, b, c, d, e, f], _, hnd =>
      have := hreach a b c d e f hnd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with h | h | h | h | h <;> rw [h] <;> simp [tightVal] <;>
        first
        | linarith
        | (refine ⟨?_, ?_, ?_⟩ <;> linarith)
        | (rw [max_eq_left (by linarith)]; linarith)
        | (rw [max_eq_right (by linarith)]; linarith)
  · unfold RoundRobinEq.CancelableBluff.IsRanking tightDeviation
    decide
  · decide
  · simp [tightVal]
    rw [max_eq_left (by linarith)]; ring
