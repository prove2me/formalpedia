-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_deletion_closed__p2m_eee70f1a_2d3d_4378_a78c_629ec2b9156c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:37:15.963532+00:00
-- url     : https://prove2.me/submissions/44ee635e-5a9b-48a4-a9d3-27662b6b5734

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G F : SimpleGraph V)
    (hGF : G.edgeSet ⊆ F.edgeSet)
    (hF : WilliamsonShmoys.HasPlanarDrawingOn F) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by
  rcases hF with ⟨p, arc, hp, hedges, hcrossings⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hGuv
    apply hedges u v huv
    exact F.mem_edgeSet.mpr (hGF (G.mem_edgeSet.mpr hGuv))
  · intro u v x y huv hxy hGuv hGxy hne t ht s hs hEq
    exact hcrossings u v x y huv hxy
      (F.mem_edgeSet.mpr (hGF (G.mem_edgeSet.mpr hGuv)))
      (F.mem_edgeSet.mpr (hGF (G.mem_edgeSet.mpr hGxy)))
      hne t ht s hs hEq