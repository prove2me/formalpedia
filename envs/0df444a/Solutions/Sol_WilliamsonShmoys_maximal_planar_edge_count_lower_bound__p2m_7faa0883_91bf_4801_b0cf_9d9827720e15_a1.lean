-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_7faa0883_91bf_4801_b0cf_9d9827720e15_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:54:31.703082+00:00
-- url     : https://prove2.me/submissions/90515b0c-1c4f-4809-866b-14b4624d30a8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_triangulated_completion__p2m_42a32245_904d_4102_8e18_0dd359dce9a3_a2
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hDraw : HasPlanarDrawingOn L)
    (hMax : forall M : SimpleGraph V, L <= M -> HasPlanarDrawingOn M -> M = L) :
    3 * Fintype.card V <= L.edgeSet.ncard + 6 := by
  obtain ⟨M, hLM, hMDraw, hCount⟩ :=
    WilliamsonShmoys.maximal_planar_triangulated_completion__p2m_42a32245_904d_4102_8e18_0dd359dce9a3_a2
      L hV hDraw
  have hEq : M = L := hMax M hLM hMDraw
  rw [hEq] at hCount
  omega