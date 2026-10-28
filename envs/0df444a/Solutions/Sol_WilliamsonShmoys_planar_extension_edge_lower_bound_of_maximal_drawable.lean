-- Prove2me | solution 1 for WilliamsonShmoys.planar_extension_edge_lower_bound_of_maximal_drawable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T11:49:24.225801+00:00
-- url     : https://prove2.me/submissions/b40a8b93-2c7d-445a-97b0-479c0299c68a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_extension_exists_large_edge_supergraph

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G)
    (hmax : ∀ Z : SimpleGraph V, G ≤ Z → HasPlanarDrawingOn Z → Z ≤ G) :
    3 * Fintype.card V ≤ G.edgeSet.ncard + 6 := by
  obtain ⟨Z, hGZ, hZ, hbound⟩ :=
    WilliamsonShmoys.planar_extension_exists_large_edge_supergraph G hV hG
  have hZG : Z ≤ G := hmax Z hGZ hZ
  have hcard : Z.edgeSet.ncard ≤ G.edgeSet.ncard :=
    Set.ncard_mono (SimpleGraph.edgeSet_mono hZG)
  omega