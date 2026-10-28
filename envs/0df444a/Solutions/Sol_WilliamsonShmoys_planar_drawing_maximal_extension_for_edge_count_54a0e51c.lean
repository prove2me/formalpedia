-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension_for_edge_count_54a0e51c
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T12:08:02.775757+00:00
-- url     : https://prove2.me/submissions/8fe0564c-43fe-4e73-a9e8-43bb8800637c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V,
        L.edgeSet ⊆ M.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        M.edgeSet ⊆ L.edgeSet := by
  classical
  let candidates : Set (SimpleGraph V) :=
    {G | K.edgeSet ⊆ G.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn G}
  have h_candidates_nonempty : candidates.Nonempty := by
    exact ⟨K, Set.Subset.rfl, hK⟩
  have h_candidates_finite : candidates.Finite := Set.toFinite candidates
  obtain ⟨L, hL, hmax⟩ :=
    Set.exists_max_image candidates (fun G => G.edgeSet.encard)
      h_candidates_finite h_candidates_nonempty
  refine ⟨L, hL.1, hL.2, ?_⟩
  intro M hLM hM
  have hKM : K.edgeSet ⊆ M.edgeSet := hL.1.trans hLM
  have hM_candidates : M ∈ candidates := ⟨hKM, hM⟩
  have hcard : M.edgeSet.encard ≤ L.edgeSet.encard := hmax M hM_candidates
  have hsets : L.edgeSet = M.edgeSet :=
    (Set.toFinite L.edgeSet).eq_of_subset_of_encard_le hLM hcard
  simpa [hsets]