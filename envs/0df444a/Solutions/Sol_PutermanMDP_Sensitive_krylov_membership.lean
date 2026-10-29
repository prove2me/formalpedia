-- Prove2me | solution 1 for PutermanMDP.Sensitive.krylov_membership
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T03:04:40.748257+00:00
-- url     : https://prove2.me/submissions/8b6c02e8-ecd7-4fd5-9fac-38f802f40cfd

import Mathlib

theorem solution : ¬ (∀ (m : ℕ) (H : Matrix (Fin m) (Fin m) ℝ)
    (U : Submodule ℝ (Fin m → ℝ)) (x : Fin m → ℝ)
    (h : ∀ k : ℕ, 1 ≤ k → k ≤ min H.rank (Module.finrank ℝ U) →
      (H ^ k).mulVec x ∈ U),
    ∀ k : ℕ, 1 ≤ k → (H ^ k).mulVec x ∈ U) := by
  intro hall
  have := hall 1 1 ⊥ (fun _ => 1) (fun k hk hk2 => by
    simp only [finrank_bot, Nat.le_zero, min_eq_right (Nat.zero_le _)] at hk2
    omega) 1 le_rfl
  simp only [pow_one, Matrix.one_mulVec, Submodule.mem_bot] at this
  have h0 := congrFun this 0
  simp at h0

