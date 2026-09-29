-- Prove2me | solution 1 for WhitneyEmbedding.finite_injective_immersion_from_separating_family
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-11T15:26:05.23476+00:00
-- url     : https://prove2.me/submissions/e744bde7-f026-45b3-949a-72a4c56f3b39
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WhitneyEmbedding_smooth_proper_function_of_noncompact
import Theorems.Thm_WhitneyEmbedding_exists_uniform_dim_immersion_on_compacts
import Theorems.Thm_WhitneyEmbedding_injective_immersion_of_blockwise_immersions

open Function Filter Module Set Topology
open scoped Manifold ContDiff

open WhitneyEmbedding in
theorem solution (n : ℕ)
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [T2Space M] [SecondCountableTopology M]
    (seq : ℕ → M → ℝ)
    (hseq_diff : ∀ k, ContMDiff (𝓡 n) 𝓘(ℝ) ∞ (seq k))
    (hseq_comp : ∀ k, HasCompactSupport (seq k))
    (hseq_sep : ∀ x y, x ≠ y → ∃ k, seq k x ≠ seq k y)
    (hseq_tan : ∀ x, ∀ (v : TangentSpace (𝓡 n) x), v ≠ 0 → ∃ k, mfderiv (𝓡 n) 𝓘(ℝ) (seq k) x v ≠ 0) :
    ∃ (N : ℕ) (e : M → EuclideanSpace ℝ (Fin N)),
      ContMDiff (𝓡 n) (𝓡 N) ∞ e ∧ Injective e ∧
      (∀ x, Injective (mfderiv (𝓡 n) (𝓡 N) e x)) := by
  by_cases hM : CompactSpace M
  · obtain ⟨N, e, he, hemb, hd⟩ :=
      exists_embedding_euclidean_of_compact (I := 𝓡 n) (M := M)
    exact ⟨N, e, he, hemb.injective, hd⟩
  · obtain ⟨r, hr, hrp⟩ := smooth_proper_function_of_noncompact n hM
    obtain ⟨m, hm⟩ := exists_uniform_dim_immersion_on_compacts (M := M) n
    choose g hg hginj hgimm using fun j : ℤ =>
      hm (r ⁻¹' (Set.Icc ((j : ℝ) - 1) ((j : ℝ) + 1))) (hrp.isCompact_preimage isCompact_Icc)
    exact injective_immersion_of_blockwise_immersions n m r hr g hg hginj hgimm
