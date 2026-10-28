-- Prove2me | solution 1 for WilliamsonShmoys.exists_drawable_supergraph_edge_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:52:19.008855+00:00
-- url     : https://prove2.me/submissions/ce2a8b45-058c-4187-ad5e-413902136416
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_drawable_edge_maximal_supergraph
import Theorems.Thm_WilliamsonShmoys_edge_bound_of_drawable_maximal

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hLdraw : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by
  obtain ⟨M, hLM, hMdraw, hMmax⟩ :=
    WilliamsonShmoys.exists_drawable_edge_maximal_supergraph L hLdraw
  exact ⟨M, hLM, hMdraw,
    WilliamsonShmoys.edge_bound_of_drawable_maximal M hV hMdraw hMmax⟩