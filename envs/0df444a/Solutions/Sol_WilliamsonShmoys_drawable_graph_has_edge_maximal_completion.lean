-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_has_edge_maximal_completion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T06:55:27.410469+00:00
-- url     : https://prove2.me/submissions/1d0145b7-5ca4-47f5-bddb-8538defc15e6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hV : 3 <= Fintype.card V) :
    ∃ U : SimpleGraph V,
      (∀ {u v}, T.Adj u v → U.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn U ∧
      (∀ W : SimpleGraph V,
        (∀ {u v}, U.Adj u v → W.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn W → W = U) := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun H : SimpleGraph V => T ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H)).exists_max_image
    (fun H => H.edgeFinset.card) ⟨T, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hdraw⟩⟩
  obtain ⟨hPQ, hQ⟩ : T ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
  refine ⟨Q, fun h => hPQ h, hQ, fun R hQR' hR => ?_⟩
  have hQR : Q ≤ R := fun _ _ h => hQR' h
  by_contra hne
  have hlt : Q < R := lt_of_le_of_ne hQR (Ne.symm hne)
  have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
  have h3 := hmax R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ.trans hQR, hR⟩)
  omega
