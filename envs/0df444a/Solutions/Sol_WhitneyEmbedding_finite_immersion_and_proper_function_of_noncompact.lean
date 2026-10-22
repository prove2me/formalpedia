-- Prove2me | solution 1 for WhitneyEmbedding.finite_immersion_and_proper_function_of_noncompact
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-11T11:43:29.843419+00:00
-- url     : https://prove2.me/submissions/2e320bff-3dd5-461d-81ff-5e170119a4a5

import Mathlib
import Theorems.Thm_WhitneyEmbedding_smooth_proper_function_of_noncompact
import Theorems.Thm_WhitneyEmbedding_finite_injective_immersion

open Function Filter Module Set Topology
open scoped Manifold ContDiff

theorem solution (n : ℕ)
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [T2Space M] [SecondCountableTopology M]
    (hM : ¬ CompactSpace M) :
    ∃ (N : ℕ) (e : M → EuclideanSpace ℝ (Fin N)) (r : M → ℝ),
      ContMDiff (𝓡 n) (𝓡 N) ∞ e ∧ Injective e ∧
      (∀ x, Injective (mfderiv (𝓡 n) (𝓡 N) e x)) ∧
      ContMDiff (𝓡 n) 𝓘(ℝ) ∞ r ∧ IsProperMap r := by
  obtain ⟨r, hr_diff, hr_proper⟩ := WhitneyEmbedding.smooth_proper_function_of_noncompact n hM
  obtain ⟨N, e, he_diff, he_inj, he_deriv⟩ := WhitneyEmbedding.finite_injective_immersion n hM
  exact ⟨N, e, r, he_diff, he_inj, he_deriv, hr_diff, hr_proper⟩
