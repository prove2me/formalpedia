-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_maximal_supergraph_exists_same_vertices
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T06:58:00.9494+00:00
-- url     : https://prove2.me/submissions/666d862d-8278-4e3e-8e98-c5a68d0e49c8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn K ∧ G ≤ K ∧
      ∀ L : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn L →
        K ≤ L → L ≤ K := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun H : SimpleGraph V => G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H)).exists_max_image
    (fun H => H.edgeFinset.card) ⟨G, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hG⟩⟩
  obtain ⟨hPQ, hQ⟩ : G ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
  refine ⟨Q, hQ, hPQ, fun R hR hQR => ?_⟩
  have hEq : R = Q := by
    by_contra hne
    have hlt : Q < R := lt_of_le_of_ne hQR (Ne.symm hne)
    have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
    have h3 := hmax R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ.trans hQR, hR⟩)
    omega
  exact hEq.le
