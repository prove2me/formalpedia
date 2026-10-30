-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_f8388283_f9ed_4c0f_b0f7_c6403411f5ff_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:29:21.079501+00:00
-- url     : https://prove2.me/submissions/a3ddf950-5bc3-4145-bffb-f4705565fdb1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion__p2m_726fe57b_9b66_48eb_a490_e0e9926cc417_a1
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hX : WilliamsonShmoys.HasPlanarDrawingOn X)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ Y : SimpleGraph V, X ≤ Y → WilliamsonShmoys.HasPlanarDrawingOn Y → Y = X) :
    3 * Fintype.card V ≤ X.edgeSet.ncard + 6 := by
  obtain ⟨Y, hXY, hY, hcard⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_completion__p2m_726fe57b_9b66_48eb_a490_e0e9926cc417_a1 X hX hV
  have hYX : Y = X := hmax Y hXY hY
  rw [hYX] at hcard
  omega