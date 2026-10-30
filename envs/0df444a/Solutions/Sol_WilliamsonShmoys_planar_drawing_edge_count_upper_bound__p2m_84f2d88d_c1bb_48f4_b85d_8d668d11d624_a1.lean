-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_84f2d88d_c1bb_48f4_b85d_8d668d11d624_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:45:17.074027+00:00
-- url     : https://prove2.me/submissions/bf07ddd6-e668-4f44-98ec-5f6520a74dc2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_edge_count__p2m_adaa59b8_bbaf_4393_8e55_4a0450b92ec8_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨N, _hMN, _hNPlanar, hCountLE, hNCount⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension_edge_count__p2m_adaa59b8_bbaf_4393_8e55_4a0450b92ec8_a1
      M hM hCard
  rw [hNCount] at hCountLE
  omega