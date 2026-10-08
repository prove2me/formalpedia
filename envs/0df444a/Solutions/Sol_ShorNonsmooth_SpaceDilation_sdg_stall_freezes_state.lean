-- Prove2me | solution 1 for ShorNonsmooth.SpaceDilation.sdg_stall_freezes_state
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-04T22:23:41.030974+00:00
-- url     : https://prove2.me/submissions/3c14c6e4-43a8-4ab9-b499-31b9a95022e1

import Mathlib
import Definitions.Def_ShorNonsmooth_SpaceDilation_SDGMethod

open ShorNonsmooth.SpaceDilation

/-- A stalling step freezes the state; hence the whole tail equals `s_j`. -/
theorem solution {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (h : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (α : ℕ → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n))
    (B₀ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (j : ℕ) (hgj : g (sdg g h α x₀ B₀ j).x = 0)
    (r : ℕ) (hjr : j ≤ r) :
    sdg g h α x₀ B₀ r = sdg g h α x₀ B₀ j := by
  induction r, hjr using Nat.le_induction with
  | base => rfl
  | succ r hjr ih =>
      have hg : g (sdg g h α x₀ B₀ r).x = 0 := by rw [ih]; exact hgj
      -- `sdg g h α x₀ B₀ (r + 1)` unfolds to `sdgStep g h α r (sdg … r)` unconditionally,
      -- and the `if g … = 0 then sdg … else …` guard lives *inside* `sdgStep`.  So unfolding
      -- `sdg` alone (7005) leaves `sdgStep … = sdg …`; both have to be unfolded.
      have hrep : sdg g h α x₀ B₀ (r + 1) = sdg g h α x₀ B₀ r := by
        simp [sdg, sdgStep, hg]
      rw [hrep, ih]
