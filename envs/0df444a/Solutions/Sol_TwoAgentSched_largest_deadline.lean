-- Prove2me | solution 1 for TwoAgentSched.largest_deadline
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-07T02:26:43.01569+00:00
-- url     : https://prove2.me/submissions/132eeeae-aae2-4de0-a6e0-897511a9464a

import Mathlib
import Definitions.Def_TwoAgentSched_IsDeadline

open TwoAgentSched

/-- If every job's deadline cut represents its cost function and `kstar` has the largest
deadline among the remaining jobs `U`, then at any time `τ ≥ 0` some job of `U` meets the
bound `Q` exactly when `kstar` does. -/
theorem solution {nB : ℕ} (fB : Fin nB → ℝ → ℝ) (Q : ℝ)
    (D : Fin nB → WithTop (ℝ ×ₗ Bool)) (hD : ∀ k, IsDeadline (fB k) Q (D k))
    (U : Finset (Fin nB)) (kstar : Fin nB) (hk : kstar ∈ U) (hmax : ∀ k ∈ U, D k ≤ D kstar)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    (∃ k ∈ U, fB k τ ≤ Q) ↔ fB kstar τ ≤ Q := by
  constructor
  · rintro ⟨k, hkU, hk⟩
    have hle : ((toLex (τ, true) : ℝ ×ₗ Bool) : WithTop (ℝ ×ₗ Bool)) ≤ D k :=
      (hD k τ hτ).mp hk
    exact (hD kstar τ hτ).mpr (le_trans hle (hmax k hkU))
  · intro hQ
    exact ⟨kstar, hk, hQ⟩
