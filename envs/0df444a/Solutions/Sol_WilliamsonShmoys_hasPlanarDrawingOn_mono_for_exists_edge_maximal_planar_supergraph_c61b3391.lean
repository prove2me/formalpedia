-- Prove2me | solution 1 for WilliamsonShmoys.hasPlanarDrawingOn_mono_for_exists_edge_maximal_planar_supergraph_c61b3391
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:30:06.448511+00:00
-- url     : https://prove2.me/submissions/41bd2927-7726-485f-a8ea-4d553c9b1e52

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} (hGH : G ≤ H)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by
  rcases hH with ⟨p, arc, hp, hEdges, hCrossings⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hG
    exact hEdges u v huv (hGH hG)
  · intro u v x y huv hxy hG hG' hne t ht s hs heq
    exact hCrossings u v x y huv hxy (hGH hG) (hGH hG') hne t ht s hs heq