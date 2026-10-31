-- Prove2me | solution 1 for WilliamsonShmoys.drawing_of_subgraph__p2m_4d37fe7f_2e72_452b_8439_d9da71f76f12_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:20:38.001013+00:00
-- url     : https://prove2.me/submissions/8ad0d3f3-0eb0-4bfe-aa8c-1d61916b17f3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H G : SimpleGraph V)
    (hHG : H.edgeSet ⊆ G.edgeSet)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    WilliamsonShmoys.HasPlanarDrawingOn H := by
  rcases hG with ⟨p, arc, hp, hcurves, hcrossings⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hHuv
    have hGuv : G.Adj u v := by
      apply G.mem_edgeSet.mp
      apply hHG
      exact H.mem_edgeSet.mpr hHuv
    exact hcurves u v huv hGuv
  · intro u v x y huv hxy hHuv hHxy hne t ht s hs heq
    have hGuv : G.Adj u v := by
      apply G.mem_edgeSet.mp
      apply hHG
      exact H.mem_edgeSet.mpr hHuv
    have hGxy : G.Adj x y := by
      apply G.mem_edgeSet.mp
      apply hHG
      exact H.mem_edgeSet.mpr hHxy
    exact hcrossings u v x y huv hxy hGuv hGxy hne t ht s hs heq