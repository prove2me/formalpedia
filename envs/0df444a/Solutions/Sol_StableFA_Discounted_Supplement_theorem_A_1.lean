-- Prove2me | solution 1 for StableFA.Discounted.Supplement.theorem_A_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:26:39.736447+00:00
-- url     : https://prove2.me/submissions/4a3dd755-5420-4cae-a206-2bfa8a3c589c

import Mathlib
import Definitions.Def_BertsekasSSPModel
import Definitions.Def_StableFA_Discounted_Supplement_QBackup
import Definitions.Def_StableFA_Discounted_Supplement_PairAverager

open StableFA
open StableFA.Discounted
open StableFA.Discounted.Supplement

/-- Theorem A.1: backing up and then fitting is the Q-backup of the explicit derived MDP. -/
theorem solution {n : ℕ} {C : Type} [Fintype C] [DecidableEq C]
    (M : BertsekasSSPModel n C) (A : PairAverager M) (γ : ℝ) :
    A.apply ∘ qBackup M γ = qBackup (derivedModel M A) γ := by
      classical
      funext Q z c
      let V : Fin n → ℝ := fun y => (M.U y).inf' (M.hU y) (Q y)
      have hsum :
          (∑ x, ∑ a, A.β z c x a * (∑ y, M.p x a.val y * V y)) =
            ∑ y, (∑ x, ∑ a, A.β z c x a * M.p x a.val y) * V y := by
        calc
          _ = ∑ x, ∑ y, ∑ a, (A.β z c x a * M.p x a.val y) * V y := by
            apply Finset.sum_congr rfl
            intro x hx
            simp only [Finset.mul_sum, ← mul_assoc]
            rw [Finset.sum_comm]
          _ = _ := by
            rw [Finset.sum_comm]
            simp only [Finset.sum_mul]
      change A.βc z c * A.k z c +
          (∑ x, ∑ a, A.β z c x a * (M.g x a.val + γ * ∑ y, M.p x a.val y * V y)) =
        (∑ x, ∑ a, A.β z c x a * M.g x a.val) + A.βc z c * A.k z c +
          γ * ∑ y, (∑ x, ∑ a, A.β z c x a * M.p x a.val y) * V y
      have hdist :
          (∑ x, ∑ a, A.β z c x a * (M.g x a.val + γ * ∑ y, M.p x a.val y * V y)) =
          (∑ x, ∑ a, A.β z c x a * M.g x a.val) +
            γ * (∑ x, ∑ a, A.β z c x a * (∑ y, M.p x a.val y * V y)) := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro a ha
        ring
      rw [hdist, hsum]
      ring
