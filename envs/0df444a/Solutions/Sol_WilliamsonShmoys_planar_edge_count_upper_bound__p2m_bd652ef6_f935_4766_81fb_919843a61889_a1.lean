-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_bd652ef6_f935_4766_81fb_919843a61889_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:36:08.698342+00:00
-- url     : https://prove2.me/submissions/5fdd7752-f8b6-4a51-a496-80c149073ff3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_26e2da54_dd0c_435f_9e8a_3d66581789dc_a1
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V) (hY : WilliamsonShmoys.HasPlanarDrawingOn Y)
    (hV : 3 ≤ Fintype.card V) : Y.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hsub, hcard, htri⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_26e2da54_dd0c_435f_9e8a_3d66581789dc_a1
      Y hY hV
  omega