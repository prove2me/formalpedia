-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_count_upper_bound_53dddbcd_67dc_454e_b4d2_26f3b045c421
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T07:33:13.917632+00:00
-- url     : https://prove2.me/submissions/8aa923d4-9992-4b35-9f71-8b4a2156fd13
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_1bec9fe1_f96d_4d95_8b96_08ac82faf267_a8
import Theorems.Thm_WilliamsonShmoys_connected_planar_face_accounting__p2m_1bec9fe1_f96d_4d95_8b96_08ac82faf267_a7
set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    (M.edgeSet.ncard : Int) <= 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨N, _hMN, hConn, hDraw, hEdges⟩ :=
    WilliamsonShmoys.planar_drawing_connected_extension__p2m_1bec9fe1_f96d_4d95_8b96_08ac82faf267_a8 M hM
  obtain ⟨f, hEuler, hFaceLengths⟩ :=
    WilliamsonShmoys.connected_planar_face_accounting__p2m_1bec9fe1_f96d_4d95_8b96_08ac82faf267_a7
      N hV hConn hDraw
  omega