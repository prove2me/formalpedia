-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph_same_vertex_set
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T09:24:36.672988+00:00
-- url     : https://prove2.me/submissions/c937674a-27a4-4e72-aea0-2e2b43237642

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hLdraw : WilliamsonShmoys.HasPlanarDrawingOn L) :
    Exists fun H : SimpleGraph V =>
      WilliamsonShmoys.HasPlanarDrawingOn H /\
      L.edgeSet ⊆ H.edgeSet /\
      ∀ K : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn K →
        H.edgeSet ⊂ K.edgeSet → False := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun H : SimpleGraph V => L ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H)).exists_max_image
    (fun H => H.edgeFinset.card) ⟨L, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hLdraw⟩⟩
  obtain ⟨hPQ, hQ⟩ : L ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
  refine ⟨Q, hQ, SimpleGraph.edgeSet_subset_edgeSet.mpr hPQ, fun R hR hss => ?_⟩
  have hlt : Q < R := SimpleGraph.edgeSet_ssubset_edgeSet.mp hss
  have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
  have h3 := hmax R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ.trans hlt.le, hR⟩)
  omega
