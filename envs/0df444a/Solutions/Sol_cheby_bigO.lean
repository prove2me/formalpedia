-- Prove2me | solution 1 for cheby.bigO
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:30:43.102206+00:00
-- url     : https://prove2.me/submissions/d6c06535-2d56-4e8a-8bfb-79f5175f925c

import Definitions.Def_PrimeNumberTheoremAnd_Wiener
set_option autoImplicit true
open Filter Asymptotics
variable {f : ℕ → ℂ}

theorem solution (h : (∃ C : ℝ, ∀ n : ℕ, cumsum (fun k : ℕ ↦ ‖(f k : ℂ)‖) n ≤ C * n)) :
    cumsum (‖f ·‖) =O[atTop] ((↑) : ℕ → ℝ) := by
  obtain ⟨C, hC⟩ := h
  rw [Asymptotics.isBigO_iff]
  refine ⟨C, Filter.Eventually.of_forall (fun n ↦ ?_)⟩
  have hnonneg : 0 ≤ cumsum (fun k : ℕ ↦ ‖f k‖) n := by
    unfold cumsum
    positivity
  rw [Real.norm_of_nonneg hnonneg]
  simpa using hC n
