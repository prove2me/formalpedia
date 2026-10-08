-- Prove2me | solution 1 for PDASNewton.MMatrix.complementarity_A1
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T08:46:55.526067+00:00
-- url     : https://prove2.me/submissions/b9273794-7ce6-47eb-aaa0-df6ff1987043

import Mathlib
import Definitions.Def_PDASNewton_MMatrix_Setting

open Filter Topology Matrix

namespace PDASNewton.MMatrix

theorem complementarity_A1 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (f ψ : Fin n → ℝ) (c : ℝ)
    (y lam : ℕ → Fin n → ℝ) (hrun : PDASNewton.Local.IsRun A f ψ c y lam) :
    ∀ k, 1 ≤ k → ∀ i, lam k i = 0 ∨ y k i = ψ i := by
  intro k hk i
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hs := hrun j
  by_cases h : 0 < lam j i + c * (y j i - ψ i)
  · exact Or.inr (hs.2.1 i h)
  · exact Or.inl (hs.2.2 i (le_of_not_gt h))


end PDASNewton.MMatrix

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (f ψ : Fin n → ℝ) (c : ℝ)
    (y lam : ℕ → Fin n → ℝ) (hrun : PDASNewton.Local.IsRun A f ψ c y lam) :
    ∀ k, 1 ≤ k → ∀ i, lam k i = 0 ∨ y k i = ψ i := PDASNewton.MMatrix.complementarity_A1 A f ψ c y lam hrun

#print axioms solution
