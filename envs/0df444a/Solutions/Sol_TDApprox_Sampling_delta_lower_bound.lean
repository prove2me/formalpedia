-- Prove2me | solution 1 for TDApprox.Sampling.delta_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T22:33:56.913039+00:00
-- url     : https://prove2.me/submissions/4d5b70e2-0990-4308-9d49-3c455e53cfda

import Mathlib
import Definitions.Def_TDApprox_Sampling_Model
open TDApprox.Sampling
theorem solution
    (α p₁ p₂ q₁ q₂ : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hpsum : p₁ + p₂ ≤ 1)
    (hpbig : 5 / (6 * α) < p₂)
    (hq₂ : 0 ≤ q₂) (hqle : q₂ ≤ q₁) (hq₁ : 0 < q₁) :
    (6 * α * p₂ - 5) * q₁ ≤
        (α * p₁ + 2 * α * p₂ - 1) * q₁ +
          2 * (α * p₁ + 2 * α * p₂ - 2) * q₂ ∧
      0 < 6 * α * p₂ - 5 := by
  have ha : 0 < 6 * α := by positivity
  have hb := (div_lt_iff₀ ha).mp hpbig
  have h1 : α * p₁ ≤ α * (1 - p₂) := mul_le_mul_of_nonneg_left (by linarith) hα0.le
  have h2 : α * p₂ ≤ α := mul_le_of_le_one_right hα0.le (by linarith)
  have hn : α * p₁ + 2 * α * p₂ - 2 ≤ 0 := by nlinarith
  have hm := mul_le_mul_of_nonpos_left hqle hn
  have hpq := mul_nonneg (mul_nonneg hα0.le hp₁) hq₁.le
  constructor
  · nlinarith
  · nlinarith
#print axioms solution

