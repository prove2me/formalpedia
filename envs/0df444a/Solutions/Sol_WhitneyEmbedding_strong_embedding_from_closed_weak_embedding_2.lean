-- Prove2me | solution 2 for WhitneyEmbedding.strong_embedding_from_closed_weak_embedding
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-11T17:20:44.26321+00:00
-- url     : https://prove2.me/submissions/f0182719-7165-4de4-8ec0-9d25f5b61255
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WhitneyEmbedding_exists_proper_self_transverse_immersion
import Theorems.Thm_WhitneyEmbedding_injective_immersion_of_self_transverse_immersion
import Theorems.Thm_WhitneyEmbedding_strong_embedding_low_dimensions
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
  by_cases hn2 : n ≤ 2
  · exact WhitneyEmbedding.strong_embedding_low_dimensions n hn hn2 e he hei hed
  · have hn3 : 3 ≤ n := by omega
    obtain ⟨f, hf, hfp, hfd, hft⟩ :=
      WhitneyEmbedding.exists_proper_self_transverse_immersion n hn e he hei hed
    obtain ⟨g, hg, hginj, hgp, hgd⟩ :=
      WhitneyEmbedding.injective_immersion_of_self_transverse_immersion n hn3 f hf hfp hfd hft
    exact ⟨g, hg, WhitneyEmbedding.proper_injective_is_embedding hgp hginj, hgd⟩
