-- Prove2me | solution 1 for VpVnp.no_poly_size_over_real
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:55:06.123162+00:00
-- url     : https://prove2.me/submissions/60fc596a-4bac-4420-8018-75c58efadeb2

import Theorems.Thm_VpVnp_permanent_over_real

/-! Corollary of the all-fields circuit lower bound of Claude (Anthropic), *VP ≠ VNP over every field*,
https://hexagonmath.org/2611.00954v1 . -/

open VpVnp

theorem solution :
    ∀ C : ℕ, ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s : ℕ, s ≤ m ^ C → ¬ Computes (perm ℝ m) s := by
  intro C
  obtain ⟨c, hc, M, hM⟩ := VpVnp.permanent_over_real
  have ht : Filter.Tendsto (fun m : ℕ => c * Real.logb 2 m ^ (1 / 3 : ℝ)) Filter.atTop Filter.atTop :=
    ((tendsto_rpow_atTop (by norm_num)).comp
      ((Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop)).const_mul_atTop hc
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (ht.eventually_ge_atTop (C : ℝ))
  refine ⟨max 1 (max M N), fun m hm s hs hcomp => ?_⟩
  have hlower := hM m (by omega) s hcomp
  change (m : ℝ) ^ (c * Real.logb 2 m ^ (1 / 3 : ℝ)) < (s : ℝ) at hlower
  have hbase : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
  have hpow := Real.rpow_le_rpow_of_exponent_le hbase (hN m (by omega))
  rw [Real.rpow_natCast] at hpow
  have : m ^ C < s := by exact_mod_cast lt_of_le_of_lt hpow hlower
  omega
