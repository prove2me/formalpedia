-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_triangulation_supergraph_edge_count_maximal_extension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T03:48:05.791549+00:00
-- url     : https://prove2.me/submissions/265381c8-d8f3-43e6-afea-021eee2aee3c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ Q : SimpleGraph V,
      N ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q ∧
        ∀ R : SimpleGraph V,
          Q ≤ R → WilliamsonShmoys.HasPlanarDrawingOn R → R = Q := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun G : SimpleGraph V => N ≤ G ∧ HasPlanarDrawingOn G)).exists_max_image
    (fun G => G.edgeFinset.card) ⟨N, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hN⟩⟩
  obtain ⟨hPQ, hQ⟩ : N ≤ Q ∧ HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
  refine ⟨Q, hPQ, hQ, fun R hQR hR => ?_⟩
  by_contra hne
  have hlt : Q < R := lt_of_le_of_ne hQR (Ne.symm hne)
  have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
  have h3 := hmax R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ.trans hQR, hR⟩)
  omega
