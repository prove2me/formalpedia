-- Prove2me | solution 1 for WilliamsonShmoys.edge_bound_of_maximal_drawable
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:46:19.338704+00:00
-- url     : https://prove2.me/submissions/af687a28-e896-42f0-ad8b-c725e05198d1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_drawable_supergraph_edge_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hLdraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hLmax : ∀ M : SimpleGraph V,
      L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L) :
    3 * Fintype.card V - 6 ≤ L.edgeSet.ncard := by
  obtain ⟨M, hLM, hMdraw, hMbound⟩ :=
    WilliamsonShmoys.exists_drawable_supergraph_edge_bound L hV hLdraw
  have hML : M ≤ L := hLmax M hLM hMdraw
  exact hMbound.trans (Set.ncard_mono (SimpleGraph.edgeSet_mono hML))