-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_one_edge_step__p2m_5fed2e6c_fc0c_4ddf_b02b_f52b48f84d02_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:53:48.773506+00:00
-- url     : https://prove2.me/submissions/8ade66cf-c04d-476a-acc7-c3c0ab3e2883

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem S219WS.sub_draw {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} (hle : G ≤ H)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by
  obtain ⟨p, arc, hp, h1, h2⟩ := hH
  exact ⟨p, arc, hp, fun u v huv hA => h1 u v huv (hle hA),
    fun u v x y huv hxy hA hB => h2 u v x y huv hxy (hle hA) (hle hB)⟩

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G K : SimpleGraph V)
    (hSub : G.edgeSet ⊆ K.edgeSet)
    (hStrict : G.edgeSet.ncard < K.edgeSet.ncard)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      H.edgeSet.ncard = G.edgeSet.ncard + 1 ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  have hne : (K.edgeSet \ G.edgeSet).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at h
    rw [Set.Subset.antisymm hSub h] at hStrict
    exact lt_irrefl _ hStrict
  obtain ⟨e, heK, heG⟩ := hne
  have hnd : ¬ e.IsDiag := K.not_isDiag_of_mem_edgeSet heK
  let H := SimpleGraph.fromEdgeSet (insert e G.edgeSet)
  have hH : H.edgeSet = insert e G.edgeSet := by
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    ext x
    simp only [Set.mem_sdiff, Set.mem_insert_iff]
    constructor
    · exact fun h => h.1
    · rintro (rfl | hx)
      · exact ⟨Or.inl rfl, hnd⟩
      · exact ⟨Or.inr hx, G.not_isDiag_of_mem_edgeSet hx⟩
  refine ⟨H, ?_, ?_, ?_⟩
  · rw [hH]; exact Set.subset_insert _ _
  · rw [hH, Set.ncard_insert_of_notMem heG (Set.toFinite _)]
  · apply S219WS.sub_draw _ hDraw
    rw [← SimpleGraph.edgeSet_subset_edgeSet, hH]
    exact Set.insert_subset heK hSub
