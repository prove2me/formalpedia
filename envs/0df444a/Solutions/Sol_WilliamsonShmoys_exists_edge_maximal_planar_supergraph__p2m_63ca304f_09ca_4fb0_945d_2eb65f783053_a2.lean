-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_63ca304f_09ca_4fb0_945d_2eb65f783053_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T02:01:09.228326+00:00
-- url     : https://prove2.me/submissions/94723c91-242b-4c9b-9096-19fbd32a0715

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        K.edgeSet ⊆ L.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        L.edgeSet ⊆ K.edgeSet := by
  classical
  let S : Set (SimpleGraph V) :=
    {G | H ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := ⟨H, le_rfl, hDraw⟩
  obtain ⟨K, hKmax⟩ := hSfinite.exists_maximal hSnonempty
  have hKmem : K ∈ S := hKmax.1
  refine ⟨K, ?_, hKmem.2, ?_⟩
  · exact SimpleGraph.edgeSet_subset_edgeSet.mpr hKmem.1
  · intro L hKL hLdraw
    have hKL' : K ≤ L := SimpleGraph.edgeSet_subset_edgeSet.mp hKL
    have hLmem : L ∈ S := ⟨hKmem.1.trans hKL', hLdraw⟩
    have hLK : L ≤ K := hKmax.2 hLmem hKL'
    exact SimpleGraph.edgeSet_subset_edgeSet.mpr hLK