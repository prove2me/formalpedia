-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_drawable_supergraph_repair_20261027
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:18:18.662214+00:00
-- url     : https://prove2.me/submissions/0d815f88-b0bb-40e3-b3ed-93b167866c85

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W) :
    ∃ U : SimpleGraph V,
      W ≤ U ∧
      WilliamsonShmoys.HasPlanarDrawingOn U ∧
      ∀ H : SimpleGraph V, W ≤ H →
        WilliamsonShmoys.HasPlanarDrawingOn H →
        H.edgeSet.ncard ≤ U.edgeSet.ncard := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun X0 : SimpleGraph V => W ≤ X0 ∧ WilliamsonShmoys.HasPlanarDrawingOn X0)).exists_max_image
    (fun X0 => X0.edgeSet.ncard) ⟨W, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hW⟩⟩
  obtain ⟨hPQ, hQ⟩ := (Finset.mem_filter.mp hQm).2
  exact ⟨Q, hPQ, hQ, fun H h1 h2 => hmax H (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩)⟩
