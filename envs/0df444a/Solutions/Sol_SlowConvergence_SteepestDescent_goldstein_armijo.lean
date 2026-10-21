-- Prove2me | solution 1 for SlowConvergence.SteepestDescent.goldstein_armijo
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:45:19.307292+00:00
-- url     : https://prove2.me/submissions/da9d1aae-759b-400a-9a37-24791bb561b2

import Mathlib
import Definitions.Def_SlowConvergence_SteepestDescent_Data

set_option autoImplicit false
open SlowConvergence.SteepestDescent

theorem solution (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (α : ℕ → ℝ)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1) (k : ℕ)
    (hαk : 2 * (1 - b) ≤ α k ∧ α k ≤ 2 * (1 - a)) :
    -(sk τ α k * gk τ k) = α k * |gk τ k| ^ 2 ∧
      -(a * (sk τ α k * gk τ k)) ≤ fk τ α k - fk τ α (k + 1) ∧
      fk τ α k - fk τ α (k + 1) ≤ -(b * (sk τ α k * gk τ k)) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  set e : ℝ := 1 / 2 + SlowConvergence.Newton.eta τ with he
  set q : ℝ := (1 / ((k : ℝ) + 1)) ^ e with hq
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by positivity) _
  have hs : sk τ α k = α k * q := by
    simp [sk, xk, hq, he]
  have hg : gk τ k = -q := by simp [gk, hq, he]
  have hc : (1 / ((k : ℝ) + 1)) ^ (1 + 2 * SlowConvergence.Newton.eta τ) = q ^ 2 := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    rw [he]; push_cast; ring
  have hdiff : fk τ α k - fk τ α (k + 1) = α k * (1 - 1 / 2 * α k) * q ^ 2 := by
    simp only [fk]
    rw [hc]; ring
  have hαpos : 0 < α k := by linarith [hαk.1]
  rw [hs, hg, hdiff, abs_neg, abs_of_nonneg hq0]
  have hD : 0 ≤ α k * q ^ 2 := by positivity
  refine ⟨by ring, ?_, ?_⟩
  · have : α k * (1 - 1 / 2 * α k) * q ^ 2 - -(a * (α k * q * -q)) * 1
        = (1 - 1 / 2 * α k - a) * (α k * q ^ 2) := by ring
    nlinarith [mul_nonneg (by linarith [hαk.2] : (0:ℝ) ≤ 1 - 1 / 2 * α k - a) hD]
  · nlinarith [mul_nonneg (by linarith [hαk.1] : (0:ℝ) ≤ b - (1 - 1 / 2 * α k)) hD]
