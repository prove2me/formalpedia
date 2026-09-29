-- Prove2me | solution 1 for WhitneyEmbedding.finite_injective_immersion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-11T14:22:52.225274+00:00
-- url     : https://prove2.me/submissions/70aeba74-6b1a-49c7-b075-ef5993d3deb1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WhitneyEmbedding_exists_separating_smooth_functions
import Theorems.Thm_WhitneyEmbedding_finite_injective_immersion_from_separating_family

open Function Filter Module Set Topology
open scoped Manifold ContDiff

/-- Weak Whitney immersion for a noncompact manifold, reduced to two lemmas:
the existence of a countable separating family of compactly supported smooth functions,
and the passage from such a family to a finite-dimensional injective immersion. -/
theorem solution (n : ℕ)
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [T2Space M] [SecondCountableTopology M]
    (hM : ¬ CompactSpace M) :
    ∃ (N : ℕ) (e : M → EuclideanSpace ℝ (Fin N)),
      ContMDiff (𝓡 n) (𝓡 N) ∞ e ∧ Injective e ∧
      (∀ x, Injective (mfderiv (𝓡 n) (𝓡 N) e x)) := by
  obtain ⟨seq, hseq_diff, hseq_comp, hseq_sep, hseq_tan⟩ :=
    WhitneyEmbedding.exists_separating_smooth_functions (M := M) n
  exact WhitneyEmbedding.finite_injective_immersion_from_separating_family n seq
    hseq_diff hseq_comp hseq_sep hseq_tan
