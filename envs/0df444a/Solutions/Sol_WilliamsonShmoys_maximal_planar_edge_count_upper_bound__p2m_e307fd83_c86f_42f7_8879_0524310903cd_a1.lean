-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_upper_bound__p2m_e307fd83_c86f_42f7_8879_0524310903cd_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:28:04.43979+00:00
-- url     : https://prove2.me/submissions/0ac37ca7-2177-4ceb-9853-aa0c3ff3d280
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_082382e5_3572_4220_9e97_f9d8fc451c82_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hsub, hH, hmono, htri⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_082382e5_3572_4220_9e97_f9d8fc451c82_a2
      G hG hV
  omega