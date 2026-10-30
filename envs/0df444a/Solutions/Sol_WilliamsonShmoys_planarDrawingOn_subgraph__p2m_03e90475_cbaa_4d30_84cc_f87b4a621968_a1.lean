-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_subgraph__p2m_03e90475_cbaa_4d30_84cc_f87b4a621968_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T01:01:26.997933+00:00
-- url     : https://prove2.me/submissions/33207bb6-12dc-45f1-bfd7-eea95881a9b3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} (hGH : G ≤ H) (hH : HasPlanarDrawingOn H) :
    HasPlanarDrawingOn G := by
  rcases hH with ⟨p, arc, hp, hEdges, hCrossings⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hGuv
    exact hEdges u v huv (hGH hGuv)
  · intro u v x y huv hxy hGuv hGxy hne t ht s hs hEq
    exact hCrossings u v x y huv hxy (hGH hGuv) (hGH hGxy) hne t ht s hs hEq