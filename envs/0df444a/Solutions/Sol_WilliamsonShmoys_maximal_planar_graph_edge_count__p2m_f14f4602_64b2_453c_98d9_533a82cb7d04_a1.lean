-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_f14f4602_64b2_453c_98d9_533a82cb7d04_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:30:40.393871+00:00
-- url     : https://prove2.me/submissions/56a42fc5-cf54-4642-a5f2-999c62d0f62f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_completion__p2m_29d426c4_6f5c_451a_abaf_84dc0cba9aeb_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ J : SimpleGraph V, H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J = H)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 = H.edgeSet.ncard := by
  obtain ⟨J, hHJ, hJ, hCount⟩ := WilliamsonShmoys.planar_drawing_edge_completion__p2m_29d426c4_6f5c_451a_abaf_84dc0cba9aeb_a1 H hH hV
  have hEq : J = H := hmax J hHJ hJ
  simpa [hEq] using hCount