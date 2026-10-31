-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_edge_bound__p2m_bdf730fd_a18a_4f08_870b_a5969b01342b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:19:06.347223+00:00
-- url     : https://prove2.me/submissions/6ef0207d-42a7-49b6-9396-3724fae4aae3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_40bf128a_95fa_481c_8fd2_3c8143f624ef_a2
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_bound__p2m_40bf128a_95fa_481c_8fd2_3c8143f624ef_a2

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hMH, hCard, hDrawH, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_40bf128a_95fa_481c_8fd2_3c8143f624ef_a2
      M hDraw
  have hBound :=
    WilliamsonShmoys.maximal_drawable_edge_bound__p2m_40bf128a_95fa_481c_8fd2_3c8143f624ef_a2
      H hV hDrawH hMax
  omega