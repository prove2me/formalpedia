-- Prove2me | solution 1 for PDSmooth.Framework.Supplement.lemma_G_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:43:00.321375+00:00
-- url     : https://prove2.me/submissions/a2d8d312-0a4b-4965-a15a-41881ba91d2e

import Mathlib
import Definitions.Def_PDSmooth_Framework_Supplement_Alg2

open PDSmooth
open PDSmooth.Framework
open PDSmooth.Framework.Supplement

/-- Lemma G.2, p. 41: for `L̄ > 0`, the weights (5.23) (`μ = 0`: `α₀ = 1`, `α_t = (2t + 3)/4`) give
`A_t = (t + 2)²/4`, the weights (5.27) (`μ > 0`: `α₀ = 1`, `α_t = (1 + √θ)^{t−1}√θ`, `θ = μ/L̄`) give
`A_t = (1 + √θ)^t` (G.8), and in both cases `(A_tμ + L̄)A_{t+1} ≥ L̄α²_{t+1}` for all `t ≥ 0` (G.3). -/
theorem solution (μ Lbar : ℝ) (hLbar : 0 < Lbar) (α : ℕ → ℝ) :
    (μ = 0 → α 0 = 1 → (∀ t : ℕ, 1 ≤ t → α t = (2 * (t : ℝ) + 3) / 4) →
      (∀ t : ℕ, accW α t = ((t : ℝ) + 2) ^ 2 / 4) ∧
      ∀ t : ℕ, Lbar * α (t + 1) ^ 2 ≤ (accW α t * μ + Lbar) * accW α (t + 1)) ∧
    (0 < μ → α 0 = 1 →
      (∀ t : ℕ, 1 ≤ t → α t = (1 + Real.sqrt (μ / Lbar)) ^ (t - 1) * Real.sqrt (μ / Lbar)) →
      (∀ t : ℕ, accW α t = (1 + Real.sqrt (μ / Lbar)) ^ t) ∧
      ∀ t : ℕ, Lbar * α (t + 1) ^ 2 ≤ (accW α t * μ + Lbar) * accW α (t + 1)) := by
        have hsucc : ∀ t : ℕ, accW α (t + 1) = accW α t + α (t + 1) := by
          intro t
          unfold accW
          rw [Finset.sum_range_succ]
        have hzero : accW α 0 = α 0 := by
          unfold accW
          simp
        refine ⟨?_, ?_⟩
        · intro hμ h0 hα
          have hA : ∀ t : ℕ, accW α t = ((t : ℝ) + 2) ^ 2 / 4 := by
            intro t
            induction t with
            | zero => rw [hzero, h0]; norm_num
            | succ n ih =>
              rw [hsucc, ih, hα (n + 1) (by omega)]
              push_cast
              ring
          refine ⟨hA, ?_⟩
          intro t
          rw [hμ, hA (t + 1), hα (t + 1) (by omega)]
          push_cast
          have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
          have h1 : ((2 * ((t : ℝ) + 1) + 3) / 4) ^ 2 ≤ ((t : ℝ) + 1 + 2) ^ 2 / 4 := by
            nlinarith
          have := mul_le_mul_of_nonneg_left h1 hLbar.le
          nlinarith
        · intro hμ h0 hα
          set s := Real.sqrt (μ / Lbar) with hs
          have hs0 : 0 ≤ s := Real.sqrt_nonneg _
          have hs2 : s ^ 2 = μ / Lbar := Real.sq_sqrt (div_nonneg hμ.le hLbar.le)
          have hA : ∀ t : ℕ, accW α t = (1 + s) ^ t := by
            intro t
            induction t with
            | zero => rw [hzero, h0]; norm_num
            | succ n ih =>
              rw [hsucc, ih, hα (n + 1) (by omega)]
              simp only [Nat.add_sub_cancel]
              ring
          refine ⟨hA, ?_⟩
          intro t
          rw [hA t, hA (t + 1), hα (t + 1) (by omega)]
          simp only [Nat.add_sub_cancel]
          have hLs : Lbar * s ^ 2 = μ := by
            rw [hs2]; field_simp
          have hp : (1 : ℝ) ≤ (1 + s) ^ t := one_le_pow₀ (by linarith)
          have hP0 : (0 : ℝ) ≤ (1 + s) ^ t := by linarith
          have key : Lbar * ((1 + s) ^ t * s) ^ 2 = ((1 + s) ^ t) ^ 2 * μ := by
            rw [← hLs]; ring
          rw [key, pow_succ (1 + s) t]
          generalize (1 + s) ^ t = P at hp hP0 ⊢
          have hq : (0:ℝ) ≤ P ^ 2 * μ := by positivity
          nlinarith [mul_nonneg hq hs0, mul_nonneg (mul_nonneg hP0 hLbar.le) (by linarith : (0:ℝ) ≤ 1 + s)]
