-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_upper__p2m_6b45552a_e614_43a1_bcb2_5a02dc98d5fe_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:43:40.876356+00:00
-- url     : https://prove2.me/submissions/42ccb294-9c79-42eb-8ee3-86a049fa2661
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_certificate__p2m_92141bf6_e5aa_4060_bf2d_eb63ac46c206_a3
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_certificate_edge_bound__p2m_92141bf6_e5aa_4060_bf2d_eb63ac46c206_a3

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨c⟩ := WilliamsonShmoys.exists_planar_triangulation_certificate__p2m_92141bf6_e5aa_4060_bf2d_eb63ac46c206_a3
    H hDraw hV
  exact WilliamsonShmoys.planar_triangulation_certificate_edge_bound__p2m_92141bf6_e5aa_4060_bf2d_eb63ac46c206_a3
    H hV c