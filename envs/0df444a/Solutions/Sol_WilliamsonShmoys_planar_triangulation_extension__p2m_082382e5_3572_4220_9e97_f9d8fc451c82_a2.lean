-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_082382e5_3572_4220_9e97_f9d8fc451c82_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:44:32.312661+00:00
-- url     : https://prove2.me/submissions/93844fb0-c8e1-4322-b782-6b85789c0654
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_exists__p2m_e311c4a7_aff6_4403_a1d3_f4a962b82e69_a1
import Theorems.Thm_WilliamsonShmoys_planar_maximal_drawing_edge_count__p2m_e311c4a7_aff6_4403_a1d3_f4a962b82e69_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hGH, hH, hEdges, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_exists__p2m_e311c4a7_aff6_4403_a1d3_f4a962b82e69_a1
      G hG
  have hCount :=
    WilliamsonShmoys.planar_maximal_drawing_edge_count__p2m_e311c4a7_aff6_4403_a1d3_f4a962b82e69_a1
      H hH hV hMax
  exact ⟨H, hGH, hH, hEdges, hCount⟩