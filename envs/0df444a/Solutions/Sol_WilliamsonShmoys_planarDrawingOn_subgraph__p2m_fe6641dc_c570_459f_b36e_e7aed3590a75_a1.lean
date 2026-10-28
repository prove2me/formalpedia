-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_subgraph__p2m_fe6641dc_c570_459f_b36e_e7aed3590a75_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:13:48.388544+00:00
-- url     : https://prove2.me/submissions/c76a0f08-ae00-458f-88e4-f870c27452be

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (hGH : G.edgeSet ⊆ H.edgeSet)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by
  have hle : G ≤ H := SimpleGraph.edgeSet_subset_edgeSet.mp hGH
  obtain ⟨p, arc, hp, h1, h2⟩ := hH
  exact ⟨p, arc, hp, fun u v huv hA => h1 u v huv (hle hA),
    fun u v x y huv hxy hA hB => h2 u v x y huv hxy (hle hA) (hle hB)⟩
