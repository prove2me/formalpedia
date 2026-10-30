-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_f10915d7_3b63_441c_afee_bba7154a1b1e_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:20:48.163237+00:00
-- url     : https://prove2.me/submissions/99ebe22d-1e3e-4c9f-9d7d-0722bd1667d3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_207a9eb6_cad3_49f0_8490_e053d02495d4_a1
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : forall M : SimpleGraph V, Set.Subset H.edgeSet M.edgeSet ->
      WilliamsonShmoys.HasPlanarDrawingOn M -> H = M)
    (hV : 3 <= Fintype.card V) : H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hCompletion :=
    WilliamsonShmoys.planar_triangulation_completion__p2m_207a9eb6_cad3_49f0_8490_e053d02495d4_a1
      H hDraw hV
  cases hCompletion with
  | intro M hRest =>
    cases hRest with
    | intro hSub hRest =>
      cases hRest with
      | intro hDrawM hCount =>
        have hHM : H = M := hMax M hSub hDrawM
        simpa [hHM] using hCount