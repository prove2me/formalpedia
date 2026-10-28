-- Prove2me | solution 1 for avram_dividend_classical_renewal_quotient_limit_le_identity_27bb7271
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T10:34:36.714999+00:00
-- url     : https://prove2.me/submissions/ee8e58e3-09f3-4964-8fa1-410af749b29b

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
    : Filter.Tendsto (fun ε : ℝ => a - ε) (𝓝[>] (0:ℝ)) (𝓝[≠] a) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have hcont : Continuous (fun ε : ℝ => a - ε) := continuous_const.sub continuous_id
    have hsub : Filter.Tendsto (fun ε : ℝ => a - ε) (𝓝 (0:ℝ)) (𝓝 a) := by
      simpa only [sub_zero] using hcont.tendsto (0 : ℝ)
    exact hsub.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : (0:ℝ) < ε := hε
    show a - ε ≠ a
    exact fun h => ne_of_gt hε0 (by linarith)
