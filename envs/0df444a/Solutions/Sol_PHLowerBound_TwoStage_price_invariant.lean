-- Prove2me | solution 1 for PHLowerBound.TwoStage.price_invariant
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T02:43:50.260404+00:00
-- url     : https://prove2.me/submissions/596ed9ac-1a33-46bc-ac48-592d9be29fb5

import Definitions.Def_PHLowerBound_TwoStage_Setting
open PHLowerBound.TwoStage
open scoped BigOperators

theorem solution {Ξ : Type*} [Fintype Ξ]
    {n₁ p₁ n₂ p₂ m₁ m₂ : ℕ} (P : SMIP Ξ n₁ p₁ n₂ p₂ m₁ m₂)
    (ρ : ℝ) (x : ℕ → Ξ → Fin n₁ → ℝ) (y : ℕ → Ξ → Fin n₂ → ℝ)
    (xhat : ℕ → Fin n₁ → ℝ) (w : ℕ → Ξ → Fin n₁ → ℝ)
    (N : ℕ) (hrun : P.IsPHARun ρ x y xhat w N) :
    ∀ ν ≤ N, ∑ ξ, P.p ξ • w ν ξ = 0 := by
  classical
  rcases hrun with ⟨hzero, _, havg, hup, _⟩
  intro ν
  induction ν with
  | zero => simp [hzero]
  | succ ν ih =>
    intro hν
    have hi := ih (Nat.le_of_succ_le hν)
    have ha := havg (ν + 1) (by omega) hν
    have hu := hup (ν + 1) (by omega) hν
    simp only [Nat.add_sub_cancel] at hu
    simp_rw [hu, smul_add, smul_sub, smul_comm (P.p _) ρ]
    rw [Finset.sum_add_distrib, hi, zero_add, Finset.sum_sub_distrib,
      ← Finset.smul_sum, ← Finset.smul_sum, ← Finset.sum_smul,
      P.p_sum, one_smul, ← ha, sub_self]
