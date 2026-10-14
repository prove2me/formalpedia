-- Prove2me | solution 1 for PHLowerBound.TwoStage.pha_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T02:50:48.029671+00:00
-- url     : https://prove2.me/submissions/dfc5916d-df75-4025-9018-6a6df27c5ef7

import Theorems.Thm_PHLowerBound_TwoStage_price_invariant
import Theorems.Thm_PHLowerBound_TwoStage_proposition_1
open PHLowerBound.TwoStage

theorem solution {Ξ : Type*} [Fintype Ξ]
    {n₁ p₁ n₂ p₂ m₁ m₂ : ℕ} (P : SMIP Ξ n₁ p₁ n₂ p₂ m₁ m₂)
    (hX : ∀ ξ, (P.X ξ).Nonempty) (hopt : P.HasOptimalSolution)
    (ρ : ℝ) (x : ℕ → Ξ → Fin n₁ → ℝ) (y : ℕ → Ξ → Fin n₂ → ℝ)
    (xhat : ℕ → Fin n₁ → ℝ) (w : ℕ → Ξ → Fin n₁ → ℝ)
    (N : ℕ) (hN : 1 ≤ N) (hrun : P.IsPHARun ρ x y xhat w N) :
    P.D (w N) ≤ P.zStar := by
  apply proposition_1 P hX hopt (w N)
  exact price_invariant P ρ x y xhat w N hrun N le_rfl
