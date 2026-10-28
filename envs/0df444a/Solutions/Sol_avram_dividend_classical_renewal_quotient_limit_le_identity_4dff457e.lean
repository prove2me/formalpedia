-- Prove2me | solution 1 for avram_dividend_classical_renewal_quotient_limit_le_identity_4dff457e
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T10:34:43.400084+00:00
-- url     : https://prove2.me/submissions/983d225a-4a30-46d2-8dfb-0e7087b25f8b

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open scoped ENNReal

theorem solution (V : ℝ≥0∞) (W : ℝ → ℝ) (a d : ℝ) (ha : 0 < a)
    (hD : HasDerivAt W d a) (hd : d ≠ 0)
    (hWa : 0 < W a)
    (hW8 : ∀ ε : ℝ, 0 < ε → ε < a → 0 ≤ W (a - ε))
    (hlt : ∀ ε : ℝ, 0 < ε → ε < a → W (a - ε) < W a)
    (hfin : ∀ (N : ℕ) (ε : ℝ), 0 < ε → ε < a →
      ∑ k ∈ Finset.range N,
        ENNReal.ofReal ε * (ENNReal.ofReal (W (a - ε) / W a)) ^ (k + 1) ≤ V)
    (hWa0 : W a ≠ 0)
    (step : ∀ ε : ℝ, 0 < ε → ε < a →
      ENNReal.ofReal (ε * (W (a - ε) / W a) / (1 - W (a - ε) / W a)) ≤ V)
    (hWcont : Filter.Tendsto (fun ε : ℝ => W (a - ε)) (𝓝[>] (0:ℝ)) (𝓝 (W a)))
    (harg : Filter.Tendsto (fun ε : ℝ => a - ε) (𝓝[>] (0:ℝ)) (𝓝[≠] a))
    (hgap0 : Filter.Tendsto ((slope W a) ∘ (fun ε : ℝ => a - ε)) (𝓝[>] (0:ℝ)) (𝓝 d))
    : ((slope W a) ∘ (fun ε : ℝ => a - ε))
      = (fun ε : ℝ => (W a - W (a - ε)) / ε) := by
  funext ε
  by_cases hε : ε = 0
  · subst hε
    simp [sub_zero, sub_self, div_zero, inv_zero, zero_smul, mul_zero]
  · have hden : (a - ε) - a ≠ 0 := by
      have h1 : (a - ε) - a = -ε := by ring
      rw [h1]
      exact neg_ne_zero.mpr hε
    show ((a - ε) - a)⁻¹ • (W (a - ε) - W a) = (W a - W (a - ε)) / ε
    rw [smul_eq_mul]
    field_simp
    ring
