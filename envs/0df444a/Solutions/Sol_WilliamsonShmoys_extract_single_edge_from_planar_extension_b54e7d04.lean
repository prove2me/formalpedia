-- Prove2me | solution 1 for WilliamsonShmoys.extract_single_edge_from_planar_extension_b54e7d04
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T08:42:49.933214+00:00
-- url     : https://prove2.me/submissions/0f05386b-58f0-47d9-bf80-4470664b7caf

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
    (G K : SimpleGraph V)
    (hGK : G.edgeSet ⊆ K.edgeSet)
    (hKplanar : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hsmall : G.edgeSet.ncard < 3 * Fintype.card V - 6)
    (hKcount : K.edgeSet.ncard = 3 * Fintype.card V - 6) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊂ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = G.edgeSet.ncard + 1 := by
  classical
  have hlt : G.edgeSet.ncard < K.edgeSet.ncard := by omega
  obtain ⟨e, heK, heG⟩ : ∃ e ∈ K.edgeSet, e ∉ G.edgeSet := by
    by_contra h
    push_neg at h
    have : K.edgeSet ⊆ G.edgeSet := h
    have := Set.ncard_le_ncard this (Set.toFinite _)
    omega
  have hnd : ¬ e.IsDiag := K.not_isDiag_of_mem_edgeSet heK
  let H := SimpleGraph.fromEdgeSet (insert e G.edgeSet)
  have hHe : H.edgeSet = insert e G.edgeSet := by
    simp only [H, SimpleGraph.edgeSet_fromEdgeSet]
    ext x
    constructor
    · intro hx; exact hx.1
    · intro hx
      refine ⟨hx, ?_⟩
      rcases hx with rfl | hx
      · exact hnd
      · exact G.not_isDiag_of_mem_edgeSet hx
  refine ⟨H, ?_, ?_, ?_⟩
  · rw [hHe]; exact Set.ssubset_insert heG
  · refine S183mono H K ?_ hKplanar
    rw [← SimpleGraph.edgeSet_subset_edgeSet, hHe]
    exact Set.insert_subset heK hGK
  · rw [hHe, Set.ncard_insert_of_notMem heG (Set.toFinite _)]
