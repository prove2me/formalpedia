-- Prove2me | solution 1 for WilliamsonShmoys.extract_one_edge_from_drawable_extension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T11:56:52.215714+00:00
-- url     : https://prove2.me/submissions/a186590d-a02d-4334-81f9-13218b8909e6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem S183mono {V : Type} [Fintype V] [LinearOrder V] (G K : SimpleGraph V) (hGK : G ≤ K)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : WilliamsonShmoys.HasPlanarDrawingOn G := by
  obtain ⟨p, arc, hp, h1, h2⟩ := hK
  exact ⟨p, arc, hp, fun u v huv hadj => h1 u v huv (hGK hadj),
    fun u v x y huv hxy h3 h4 hne => h2 u v x y huv hxy (hGK h3) (hGK h4) hne⟩

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hneq : G ≠ H) :
    ∃ J : SimpleGraph V,
      G ≤ J ∧ WilliamsonShmoys.HasPlanarDrawingOn J ∧
      J.edgeSet.ncard = G.edgeSet.ncard + 1 := by
  classical
  have hGK : G.edgeSet ⊆ H.edgeSet := SimpleGraph.edgeSet_subset_edgeSet.2 hGH
  obtain ⟨e, heK, heG⟩ : ∃ e ∈ H.edgeSet, e ∉ G.edgeSet := by
    by_contra h
    push_neg at h
    exact hneq (SimpleGraph.edgeSet_inj.1 (Set.Subset.antisymm hGK h))
  have hnd : ¬ e.IsDiag := H.not_isDiag_of_mem_edgeSet heK
  let J := SimpleGraph.fromEdgeSet (insert e G.edgeSet)
  have hHe : J.edgeSet = insert e G.edgeSet := by
    simp only [J, SimpleGraph.edgeSet_fromEdgeSet]
    ext x
    constructor
    · intro hx; exact hx.1
    · intro hx
      refine ⟨hx, ?_⟩
      rcases hx with rfl | hx
      · exact hnd
      · exact G.not_isDiag_of_mem_edgeSet hx
  refine ⟨J, ?_, ?_, ?_⟩
  · rw [← SimpleGraph.edgeSet_subset_edgeSet, hHe]; exact Set.subset_insert _ _
  · refine S183mono J H ?_ hH
    rw [← SimpleGraph.edgeSet_subset_edgeSet, hHe]
    exact Set.insert_subset heK hGK
  · rw [hHe, Set.ncard_insert_of_notMem heG (Set.toFinite _)]
