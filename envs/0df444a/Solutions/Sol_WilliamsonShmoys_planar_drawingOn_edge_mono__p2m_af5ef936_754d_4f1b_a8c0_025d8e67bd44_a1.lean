-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_edge_mono__p2m_af5ef936_754d_4f1b_a8c0_025d8e67bd44_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:04:58.249025+00:00
-- url     : https://prove2.me/submissions/cecc538c-c4b1-48ca-801d-397cbaec5618

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (hGH : G.edgeSet ⊆ H.edgeSet)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by
  have hle : G ≤ H := SimpleGraph.edgeSet_subset_edgeSet.1 hGH
  obtain ⟨p, arc, hp, h1, h2⟩ := hH
  exact ⟨p, arc, hp, fun u v huv h => h1 u v huv (hle h),
    fun u v x y huv hxy h h' => h2 u v x y huv hxy (hle h) (hle h')⟩
