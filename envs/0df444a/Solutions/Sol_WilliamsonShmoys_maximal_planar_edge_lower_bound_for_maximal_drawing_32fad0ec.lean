-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound_for_maximal_drawing_32fad0ec
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:05:32.204574+00:00
-- url     : https://prove2.me/submissions/6e093f3d-f1a9-4a83-b79b-6957d4a79ca8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_supergraph_edge_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    3 * Fintype.card V - 6 ≤ L.edgeSet.ncard := by
  obtain ⟨M, hLM, hM, hbound⟩ :=
    WilliamsonShmoys.planar_drawing_supergraph_edge_bound L hV hL
  have hML : M = L := hmax M hLM hM
  simpa [hML] using hbound