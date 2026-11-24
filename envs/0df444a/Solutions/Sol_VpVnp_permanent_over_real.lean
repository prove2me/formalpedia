-- Prove2me | solution 1 for VpVnp.permanent_over_real
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:55:03.921454+00:00
-- url     : https://prove2.me/submissions/cc164300-7818-4c48-b391-c399bafb8ea2

import Theorems.Thm_VpVnp_main_theorem

/-! Corollary of the all-fields circuit lower bound of Claude (Anthropic), *VP ≠ VNP over every field*,
https://hexagonmath.org/2611.00954v1 . -/

open VpVnp

theorem solution : ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s : ℕ,
    Computes (perm ℝ m) s → Beyond c m s := by
  obtain ⟨c, hc, h⟩ := VpVnp.main_theorem.{0}
  obtain ⟨M, hM⟩ := h 0
  exact ⟨c, hc, M, fun m hm s => (hM ℝ m hm s).2 (by decide)⟩
