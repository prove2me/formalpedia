-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_supergraph_edge_bound_6c2b7c10
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T19:11:14.21637+00:00
-- url     : https://prove2.me/submissions/b1a938df-bd1d-4ed9-b1c7-10fb32cffc0a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_drawing_supergraph_v2
import Theorems.Thm_WilliamsonShmoys_edge_bound_of_maximal_planar_drawing_v2
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hNdraw : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ P : SimpleGraph V,
      N ≤ P ∧
      WilliamsonShmoys.HasPlanarDrawingOn P ∧
      3 * Fintype.card V - 6 ≤ P.edgeSet.ncard := by
  obtain ⟨P, hNP, hPdraw, hPmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_drawing_supergraph_v2 N hNdraw
  exact ⟨P, hNP, hPdraw,
    WilliamsonShmoys.edge_bound_of_maximal_planar_drawing_v2 P hV hPdraw hPmax⟩