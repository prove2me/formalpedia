-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weighted_root_im_integrand_ae_tendsto_upper_boundary
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-16T08:12:00.013524+00:00
-- url     : https://prove2.me/submissions/1e2c13e6-ed11-43e4-bc6c-b2b657c2ce98

import Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_im_integrand_tendsto_upper_boundary
open Filter Set MeasureTheory Topology
open scoped BigOperators

theorem solution
    (n : ℕ) (a w : ℕ → ℝ) (l r : ℝ)
    (hx : ∀ᵐ x : ℝ ∂(volume.restrict (uIcc l r : Set ℝ)), x ≠ 0)
    (hxa : ∀ i < n, ∀ᵐ x : ℝ ∂(volume.restrict (uIcc l r : Set ℝ)), x ≠ a i) :
    ∀ᵐ x : ℝ ∂(volume.restrict (uIcc l r : Set ℝ)),
      Tendsto
        (fun ε : ℝ =>
          ((∏ i ∈ Finset.range n,
            (((x : ℂ) + ε * Complex.I) - (a i : ℂ)) ^ (w i : ℂ)) /
            ((x : ℂ) + ε * Complex.I)).im)
        (𝓝[>] 0)
        (𝓝 (((∏ i ∈ Finset.range n,
            ((x : ℂ) - (a i : ℂ)) ^ (w i : ℂ)) / (x : ℂ)).im)) := by
  have hall : ∀ᵐ x : ℝ ∂(volume.restrict (uIcc l r : Set ℝ)),
      ∀ i ∈ Finset.range n, x ≠ a i := by
    apply (Finset.eventually_all (Finset.range n)).mpr
    intro i hi
    exact hxa i (Finset.mem_range.mp hi)
  filter_upwards [hx, hall] with x hx0 hxi
  exact WeightedRootIntegralIdentity.weighted_root_im_integrand_tendsto_upper_boundary
    n a w x hx0 (by
      intro i hi
      exact hxi i (Finset.mem_range.mpr hi))
