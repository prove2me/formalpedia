-- Prove2me | solution 1 for SYKFastMix.FastMixing.corollary_15
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:54:58.948115+00:00
-- url     : https://prove2.me/submissions/c72b4894-c037-4c1d-9ccd-64f2560acf5e

import Mathlib
import Theorems.Thm_SYKFastMix_FastMixing_coefficient_good_event
import Theorems.Thm_SYKFastMix_FastMixing_coefficient_bounds_to_jacobian

noncomputable section
open scoped Matrix.Norms.L2Operator
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ComplexOrder
open SYKFastMix.FastMixing

theorem solution {N : ℕ} (Q : Model N) :
  ∃ A : Set (Disorder N), MeasurableSet A ∧
    ENNReal.ofReal (1 - 2 * Real.exp (-(N : ℝ))) ≤ disorderLaw Q A ∧
    ∀ w ∈ A, SYKEdge.opNorm (hamiltonian Q w) ≤ 2 * Q.J * N ∧
      ∀ s : ℝ, 133 * Q.J * |s| < 1 →
        SYKEdge.opNorm (jacobian Q w s - 1) ≤ 133 * Q.J * |s| / (1 - 133 * Q.J * |s|) ∧
        SYKEdge.opNorm (blockM Q w s) ≤ 133 * Q.J / (1 - 133 * Q.J * |s|)^2 ∧
        HasSum (fun m : ℕ => (s : ℂ)^m • fermionCoefficient Q w m) (jacobian Q w s) ∧
        HasSum (fun m : ℕ => (s : ℂ)^m • mCoefficient Q w m) (blockM Q w s) := by
  obtain ⟨A, hA, hprob, hgood⟩ := coefficient_good_event Q
  refine ⟨A, hA, hprob, ?_⟩
  intro w hw
  obtain ⟨hH, hF, hM⟩ := hgood w hw
  exact ⟨hH, coefficient_bounds_to_jacobian Q w hF hM⟩
