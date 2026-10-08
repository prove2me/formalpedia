-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weighted_root_integrand_tendsto_upper_boundary
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-16T07:54:40.471069+00:00
-- url     : https://prove2.me/submissions/616bd59e-cc70-455b-af26-5c5fc239390c

import Theorems.Thm_WeightedRootIntegralIdentity_cpow_tendsto_real_of_upper_half_plane
open Filter Set Topology
open scoped BigOperators

theorem solution (n : ℕ) (a w : ℕ → ℝ) (x : ℝ)
    (hx : x ≠ 0) (hxa : ∀ i < n, x ≠ a i) :
    Tendsto
      (fun ε : ℝ =>
        (∏ i ∈ Finset.range n,
          (((x : ℂ) + ε * Complex.I) - (a i : ℂ)) ^ (w i : ℂ)) /
          ((x : ℂ) + ε * Complex.I))
      (𝓝[>] 0)
      (𝓝 ((∏ i ∈ Finset.range n,
          ((x : ℂ) - (a i : ℂ)) ^ (w i : ℂ)) / (x : ℂ))) := by
  have hprod : Tendsto
      (fun ε : ℝ => ∏ i ∈ Finset.range n,
        (((x : ℂ) + ε * Complex.I) - (a i : ℂ)) ^ (w i : ℂ))
      (𝓝[>] 0)
      (𝓝 (∏ i ∈ Finset.range n,
        ((x : ℂ) - (a i : ℂ)) ^ (w i : ℂ))) := by
    apply tendsto_finset_prod
    intro i hi
    have h := WeightedRootIntegralIdentity.cpow_tendsto_real_of_upper_half_plane
      (x - a i) (w i) (sub_ne_zero.mpr (hxa i (Finset.mem_range.mp hi)))
    convert h using 1 <;> simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have hden : Tendsto (fun ε : ℝ => (x : ℂ) + ε * Complex.I)
      (𝓝[>] 0) (𝓝 (x : ℂ)) := by
    have hcast : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝 0) (𝓝 0) :=
      Complex.continuous_ofReal.continuousAt
    have h : Tendsto (fun ε : ℝ => (x : ℂ) + ε * Complex.I)
        (𝓝 0) (𝓝 (x : ℂ)) := by
      simpa using tendsto_const_nhds.add (hcast.mul_const Complex.I)
    exact h.mono_left inf_le_left
  exact hprod.div hden (Complex.ofReal_ne_zero.mpr hx)
