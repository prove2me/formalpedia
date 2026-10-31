-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound__p2m_6958ede2_46bd_4413_bb7d_9bd4b5c0d4f2_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:34:16.201371+00:00
-- url     : https://prove2.me/submissions/e602807c-29b8-45c1-8881-0a25eee14927

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion__p2m_638ff1ed_8b53_4df9_8415_0aa43fe61583_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hHplanar : HasPlanarDrawingOn H) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨T, _hHT, hsub, hTcard⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_completion__p2m_638ff1ed_8b53_4df9_8415_0aa43fe61583_a1
      H hV hHplanar
  have hcard : H.edgeSet.ncard <= T.edgeSet.ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  omega