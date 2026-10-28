-- Prove2me | solution 1 for WilliamsonShmoys.triangulation_exists_edge_maximal_planar_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T14:57:11.845029+00:00
-- url     : https://prove2.me/submissions/ba996d3c-1eb2-4631-ada5-7a05824ecf7e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    ∃ U : SimpleGraph V,
      T ≤ U ∧
      WilliamsonShmoys.HasPlanarDrawingOn U ∧
      T.edgeSet.ncard ≤ U.edgeSet.ncard ∧
      (∀ W : SimpleGraph V, U ≤ W → WilliamsonShmoys.HasPlanarDrawingOn W →
        W.edgeSet.ncard ≤ U.edgeSet.ncard) := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun X0 : SimpleGraph V => T ≤ X0 ∧ WilliamsonShmoys.HasPlanarDrawingOn X0)).exists_max_image
    (fun X0 => X0.edgeFinset.card) ⟨T, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hT⟩⟩
  obtain ⟨hPQ, hQ⟩ : T ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
  have hc : ∀ X : SimpleGraph V, X.edgeSet.ncard = X.edgeFinset.card := fun X => by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  refine ⟨Q, hPQ, hQ, Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hPQ) (Set.toFinite _), ?_⟩
  intro W hQW hW
  rw [hc, hc]
  exact hmax W (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ.trans hQW, hW⟩)
