-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension_for_edge_count__p2m_2a72d934_5721_47e6_9f14_7bb2bf8ff8c2_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T11:55:36.159319+00:00
-- url     : https://prove2.me/submissions/5139ce61-a048-4c16-9023-59e229e4798c

import Definitions.Def_WilliamsonShmoys_TriangularMap
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
      K.edgeSet.ncard ≤ L.edgeSet.ncard ∧
      ∀ M : SimpleGraph V,
        L.edgeSet ⊆ M.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        M.edgeSet ⊆ L.edgeSet := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => K.edgeSet ⊆ G.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn G
  have hS : S.Nonempty := by
    refine ⟨K, Finset.mem_filter.mpr ⟨Finset.mem_univ K, ?_⟩⟩
    exact ⟨Set.Subset.rfl, hK⟩
  obtain ⟨L, hLmem, hLmax⟩ :=
    Finset.exists_max_image S (fun G => G.edgeSet.ncard) hS
  have hLprops : K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L :=
    (Finset.mem_filter.mp hLmem).2
  refine ⟨L, hLprops.1, hLprops.2, ?_, ?_⟩
  · exact hLmax K (by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨Set.Subset.rfl, hK⟩)
  · intro M hLM hMplanar
    by_contra hML
    have hMmem : M ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hLprops.1.trans hLM, hMplanar⟩
    have hstrict : L.edgeSet ⊂ M.edgeSet :=
      Set.ssubset_iff_subset_ne.mpr ⟨hLM, fun h => hML (by simpa [h])⟩
    have hcard : L.edgeSet.ncard < M.edgeSet.ncard :=
      Set.ncard_lt_ncard hstrict (Set.toFinite _)
    exact (not_le_of_gt hcard) (hLmax M hMmem)