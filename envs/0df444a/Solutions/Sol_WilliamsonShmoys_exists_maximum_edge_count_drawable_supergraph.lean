-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximum_edge_count_drawable_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T02:39:11.628304+00:00
-- url     : https://prove2.me/submissions/d771724a-eb9c-4941-8dfd-2088cee84708

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys
theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ H' : SimpleGraph V,
        K ≤ H' → WilliamsonShmoys.HasPlanarDrawingOn H' →
          H'.edgeSet.ncard ≤ H.edgeSet.ncard) := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun G : SimpleGraph V => K ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G)).exists_max_image
    (fun G => G.edgeFinset.card) ⟨K, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hK⟩⟩
  obtain ⟨hPQ, hQ⟩ : K ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
  refine ⟨Q, hPQ, hQ, fun R hR hRd => ?_⟩
  have h3 := hmax R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hR, hRd⟩)
  rw [← SimpleGraph.coe_edgeFinset R, ← SimpleGraph.coe_edgeFinset Q, Set.ncard_coe_finset,
    Set.ncard_coe_finset]
  exact h3
