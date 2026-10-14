-- Prove2me | solution 1 for WhitneyEmbedding.strong_embedding_from_closed_weak_embedding
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-11T11:54:00.518779+00:00
-- url     : https://prove2.me/submissions/8dd39f66-58e6-4813-a1f0-bce8b2d65783
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WhitneyEmbedding_exists_projection_linear_map
import Theorems.Thm_WhitneyEmbedding_proper_injective_is_embedding

open Function Filter Module Set Topology
open scoped Manifold ContDiff

theorem solution (n : ℕ) (hn : 1 ≤ n)
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [T2Space M] [SecondCountableTopology M]
    (e : M → EuclideanSpace ℝ (Fin (2 * n + 1)))
    (he : ContMDiff (𝓡 n) (𝓡 (2 * n + 1)) ∞ e) (hei : IsClosedEmbedding e)
    (hed : ∀ x, Injective (mfderiv (𝓡 n) (𝓡 (2 * n + 1)) e x)) :
    ∃ f : M → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ f ∧ IsEmbedding f ∧
      ∀ x, Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) f x) := by
  obtain ⟨L, hL_surj, hf_props⟩ := WhitneyEmbedding.exists_projection_linear_map n hn e he hei hed
  let f := L ∘ e
  have hf_diff : ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ f := hf_props.1
  have hf_inj : Injective f := hf_props.2.1
  have hf_proper : IsProperMap f := hf_props.2.2.1
  have hf_deriv : ∀ x, Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) f x) := hf_props.2.2.2
  refine ⟨f, hf_diff, ?_, hf_deriv⟩
  exact WhitneyEmbedding.proper_injective_is_embedding hf_proper hf_inj
