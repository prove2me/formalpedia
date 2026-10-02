-- Prove2me | solution 1 for TegmarkDimensionality.stable_orbit_three_dims
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T10:41:04.257684+00:00
-- url     : https://prove2.me/submissions/e592004a-a5fd-458d-a4cd-a32cbbac5ae7

import Mathlib

open Filter Topology in
theorem solution (μ k L : ℝ) (hμ : 0 < μ) (hk : 0 < k) (hL : L ≠ 0) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      ∀ᶠ r in 𝓝[≠] r₀,
        L ^ 2 / (2 * μ * r₀ ^ 2) - k / r₀ < L ^ 2 / (2 * μ * r ^ 2) - k / r := by
  have hL2 : 0 < L ^ 2 := by positivity
  have hr0 : 0 < L ^ 2 / (μ * k) := by positivity
  refine ⟨L ^ 2 / (μ * k), hr0, ?_⟩
  have hpos : ∀ᶠ r in 𝓝[≠] (L ^ 2 / (μ * k)), 0 < r :=
    nhdsWithin_le_nhds (lt_mem_nhds hr0)
  filter_upwards [hpos, self_mem_nhdsWithin] with r hr hne
  have hne' : r ≠ L ^ 2 / (μ * k) := hne
  have key : L ^ 2 / (2 * μ * r ^ 2) - k / r
      - (L ^ 2 / (2 * μ * (L ^ 2 / (μ * k)) ^ 2) - k / (L ^ 2 / (μ * k)))
      = (L ^ 2 - μ * k * r) ^ 2 / (2 * μ * L ^ 2 * r ^ 2) := by
    have hμ' : μ ≠ 0 := hμ.ne'
    have hk' : k ≠ 0 := hk.ne'
    have hr' : r ≠ 0 := hr.ne'
    have hL2' : L ^ 2 ≠ 0 := hL2.ne'
    field_simp
    ring
  have hdiff : L ^ 2 - μ * k * r ≠ 0 := by
    intro h
    apply hne'
    rw [eq_div_iff (by positivity)]
    linarith
  have hsq : 0 < (L ^ 2 - μ * k * r) ^ 2 := by positivity
  have : 0 < (L ^ 2 - μ * k * r) ^ 2 / (2 * μ * L ^ 2 * r ^ 2) := by positivity
  linarith
