-- Prove2me | solution 1 for StochasticProg.PartitionJensen.lintegral_eq_sum_cells
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T15:06:56.046901+00:00
-- url     : https://prove2.me/submissions/64408eb1-0e00-44fa-9725-a9ecc3f391a8

import Mathlib
open MeasureTheory

theorem solution {N ν : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin N)))
    (S : Fin ν → Set (EuclideanSpace ℝ (Fin N))) (hSm : ∀ l, MeasurableSet (S l))
    (hSd : Pairwise (Function.onFun Disjoint S)) (hSc : μ (⋃ l, S l)ᶜ = 0)
    (f : EuclideanSpace ℝ (Fin N) → ENNReal) :
    ∫⁻ ξ, f ξ ∂μ = ∑ l, ∫⁻ ξ in S l, f ξ ∂μ := by
  have hae : ∀ᵐ x ∂μ, x ∈ ⋃ l, S l := mem_ae_iff.mpr hSc
  have h := lintegral_iUnion (μ := μ) hSm hSd f
  rw [Measure.restrict_eq_self_of_ae_mem hae, tsum_fintype] at h
  exact h
