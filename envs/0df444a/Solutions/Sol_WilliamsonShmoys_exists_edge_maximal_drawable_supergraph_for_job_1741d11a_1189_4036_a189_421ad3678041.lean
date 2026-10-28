-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_drawable_supergraph_for_job_1741d11a_1189_4036_a189_421ad3678041
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T05:43:02.800063+00:00
-- url     : https://prove2.me/submissions/5c19e404-5160-4ac1-95a7-e5d3f11125db

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      Set.Subset L.edgeSet M.edgeSet ∧
      ∀ N : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn N →
        Set.Subset M.edgeSet N.edgeSet →
        Set.Subset N.edgeSet M.edgeSet := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun X0 : SimpleGraph V =>
      L ≤ X0 ∧ WilliamsonShmoys.HasPlanarDrawingOn X0)).exists_max_image
    (fun X0 => X0.edgeFinset.card) ⟨L, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hL⟩⟩
  obtain ⟨hLQ, hQ⟩ : L ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
  refine ⟨Q, hQ, SimpleGraph.edgeSet_subset_edgeSet.mpr hLQ, ?_⟩
  intro N hN hQN
  have hQN' : Q ≤ N := SimpleGraph.edgeSet_subset_edgeSet.mp hQN
  by_contra hne
  have hlt : Q < N := lt_of_le_of_ne hQN' (by rintro rfl; exact hne (fun _ h => h))
  have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
  have h3 := hmax N (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hLQ.trans hQN', hN⟩)
  omega
