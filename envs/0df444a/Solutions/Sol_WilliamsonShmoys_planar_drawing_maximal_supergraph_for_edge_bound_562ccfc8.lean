-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph_for_edge_bound_562ccfc8
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T05:55:59.037511+00:00
-- url     : https://prove2.me/submissions/a9b801c3-72af-4246-903c-eedbc8029f4e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun H : SimpleGraph V => N ≤ H ∧ HasPlanarDrawingOn H)).exists_max_image
    (fun H => H.edgeFinset.card) ⟨N, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hN⟩⟩
  obtain ⟨hPQ, hQ⟩ : N ≤ Q ∧ HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
  refine ⟨Q, hPQ, hQ, fun R hQR hR => ?_⟩
  by_contra hne0
  have hne : R ≠ Q := fun h => hne0 (h ▸ le_rfl)
  have hlt : Q < R := lt_of_le_of_ne hQR (Ne.symm hne)
  have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
  have h3 := hmax R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ.trans hQR, hR⟩)
  omega
