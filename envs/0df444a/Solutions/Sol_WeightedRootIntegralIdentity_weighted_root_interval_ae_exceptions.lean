-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weighted_root_interval_ae_exceptions
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-16T08:23:10.277116+00:00
-- url     : https://prove2.me/submissions/41796052-28e3-4fb3-bf09-032bbd3d6f6c

import Theorems.Thm_WeightedRootIntegralIdentity_ae_ne_const_restrict_uIcc
open Filter Set MeasureTheory
open scoped BigOperators

theorem solution (n : ℕ) (a : ℕ → ℝ) (l r : ℝ) :
    ∀ᵐ x : ℝ ∂(volume.restrict (uIcc l r : Set ℝ)),
      x ≠ 0 ∧ ∀ i < n, x ≠ a i := by
  have hzero : ∀ᵐ x : ℝ ∂(volume.restrict (uIcc l r : Set ℝ)), x ≠ 0 :=
    Measure.ae_ne (volume.restrict (uIcc l r : Set ℝ)) 0
  have hall : ∀ᵐ x : ℝ ∂(volume.restrict (uIcc l r : Set ℝ)),
      ∀ i < n, x ≠ a i := by
    have hfin : ∀ i ∈ Finset.range n,
        ∀ᵐ x : ℝ ∂(volume.restrict (uIcc l r : Set ℝ)), x ≠ a i := by
      intro i hi
      exact Measure.ae_ne (volume.restrict (uIcc l r : Set ℝ)) (a i)
    have he := (Finset.eventually_all (Finset.range n)).mpr hfin
    filter_upwards [he] with x hx
    intro i hi
    exact hx i (Finset.mem_range.mpr hi)
  filter_upwards [hzero, hall] with x hx0 hxa
  exact ⟨hx0, hxa⟩
