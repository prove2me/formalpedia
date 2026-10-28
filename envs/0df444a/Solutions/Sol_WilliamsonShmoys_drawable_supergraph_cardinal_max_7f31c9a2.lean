-- Prove2me | solution 1 for WilliamsonShmoys.drawable_supergraph_cardinal_max_7f31c9a2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T17:42:17.562952+00:00
-- url     : https://prove2.me/submissions/79d241c5-4472-47d1-a0ca-104a7d7537bc

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      G.edgeSet ⊆ K.edgeSet ∧
      HasPlanarDrawingOn K ∧
      ∀ H : SimpleGraph V,
        K.edgeSet ⊆ H.edgeSet →
        HasPlanarDrawingOn H →
        H.edgeSet.ncard ≤ K.edgeSet.ncard := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun X0 : SimpleGraph V => G ≤ X0 ∧ HasPlanarDrawingOn X0)).exists_max_image
    (fun X0 => X0.edgeFinset.card) ⟨G, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hDraw⟩⟩
  obtain ⟨hPQ, hQ⟩ : G ≤ Q ∧ HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
  have hc : ∀ X : SimpleGraph V, X.edgeSet.ncard = X.edgeFinset.card := fun X => by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  refine ⟨Q, SimpleGraph.edgeSet_subset_edgeSet.mpr hPQ, hQ, ?_⟩
  intro W hQW hW
  rw [hc, hc]
  exact hmax W (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ.trans (SimpleGraph.edgeSet_subset_edgeSet.mp hQW), hW⟩)
