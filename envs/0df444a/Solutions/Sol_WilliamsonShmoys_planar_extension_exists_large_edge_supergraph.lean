-- Prove2me | solution 1 for WilliamsonShmoys.planar_extension_exists_large_edge_supergraph
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T12:08:00.221436+00:00
-- url     : https://prove2.me/submissions/ac4a0fa3-ee00-4107-9ca0-c334af09b2cf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_maximal_planar_extension
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_bound

set_option autoImplicit false

/-- Extend a drawable graph to an inclusion-maximal drawable graph and apply the planar edge bound. -/
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ Z : SimpleGraph V, G ≤ Z ∧ WilliamsonShmoys.HasPlanarDrawingOn Z ∧
      3 * Fintype.card V ≤ Z.edgeSet.ncard + 6 := by
  obtain ⟨Z, hGZ, hZ, hmax⟩ :=
    WilliamsonShmoys.drawable_graph_has_maximal_planar_extension G hG
  exact ⟨Z, hGZ, hZ,
    WilliamsonShmoys.maximal_drawable_graph_edge_bound Z hV hZ hmax⟩