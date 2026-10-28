-- Prove2me | solution 1 for avram_dividend_classical_renewal_quotient_limit_le_pointwise_upper_bound_fa7e49e3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T10:19:04.159812+00:00
-- url     : https://prove2.me/submissions/d6bad933-87f4-49e4-9fc2-ed2fd7460b4c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_renewal_quotient_pointwise_bound_of_finite_cycle_sums

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
    : ∀ ε : ℝ, 0 < ε → ε < a →
      ENNReal.ofReal (ε * (W (a - ε) / W a) / (1 - W (a - ε) / W a)) ≤ V := by
  have hr : ∀ ε : ℝ, 0 < ε → ε < a → 0 ≤ W (a - ε) / W a ∧ W (a - ε) / W a < 1 := by
    intro ε hε0 hεa
    exact ⟨div_nonneg (hW8 ε hε0 hεa) hWa.le, (div_lt_one hWa).mpr (hlt ε hε0 hεa)⟩
  exact AvramDividend.Classical.renewal_quotient_pointwise_bound_of_finite_cycle_sums V W a ha hr hfin
