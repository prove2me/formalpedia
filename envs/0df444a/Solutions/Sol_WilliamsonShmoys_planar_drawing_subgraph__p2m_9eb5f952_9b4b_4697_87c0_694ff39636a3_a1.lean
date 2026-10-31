-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_subgraph__p2m_9eb5f952_9b4b_4697_87c0_694ff39636a3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:51:03.658903+00:00
-- url     : https://prove2.me/submissions/b479e907-366b-47e8-bd5a-ff0279b28d1c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (N K : SimpleGraph V) (hKN : K.edgeSet ⊆ N.edgeSet)
    (hDrawN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    WilliamsonShmoys.HasPlanarDrawingOn K := by
  obtain ⟨p, arc, hp, hEdges, hCrossings⟩ := hDrawN
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hK
    have hN : N.Adj u v := N.mem_edgeSet.mp (hKN (K.mem_edgeSet.mpr hK))
    exact hEdges u v huv hN
  · intro u v x y huv hxy hKuv hKxy hne t ht s hs hEq
    have hNuv : N.Adj u v := N.mem_edgeSet.mp (hKN (K.mem_edgeSet.mpr hKuv))
    have hNxy : N.Adj x y := N.mem_edgeSet.mp (hKN (K.mem_edgeSet.mpr hKxy))
    exact hCrossings u v x y huv hxy hNuv hNxy hne t ht s hs hEq