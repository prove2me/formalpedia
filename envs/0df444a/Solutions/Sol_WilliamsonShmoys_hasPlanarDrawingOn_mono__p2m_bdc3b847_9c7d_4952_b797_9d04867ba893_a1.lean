-- Prove2me | solution 1 for WilliamsonShmoys.hasPlanarDrawingOn_mono__p2m_bdc3b847_9c7d_4952_b797_9d04867ba893_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:24:16.698198+00:00
-- url     : https://prove2.me/submissions/42553e47-5f1d-4c3d-8d28-a70970926caf

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (hHG : H.edgeSet ⊆ G.edgeSet)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    WilliamsonShmoys.HasPlanarDrawingOn H := by
  rcases hG with ⟨p, arc, hp, hdraw, hcross⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hAdj
    have hAdjG : G.Adj u v :=
      G.mem_edgeSet.mp (hHG (H.mem_edgeSet.mpr hAdj))
    exact hdraw u v huv hAdjG
  · intro u v x y huv hxy huvH hxyH hne t ht s hs hEq
    have huvG : G.Adj u v :=
      G.mem_edgeSet.mp (hHG (H.mem_edgeSet.mpr huvH))
    have hxyG : G.Adj x y :=
      G.mem_edgeSet.mp (hHG (H.mem_edgeSet.mpr hxyH))
    exact hcross u v x y huv hxy huvG hxyG hne t ht s hs hEq