-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_connected_upper__p2m_8a1edb89_91b7_4c19_a333_1779b45ebb8a_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:22:45.975534+00:00
-- url     : https://prove2.me/submissions/6d6f725d-5597-483b-a0f7-875aca20b3a2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawing_face_inequality__p2m_4d791eca_86d6_477c_bca9_50e3b58ef00f_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hconn : G.Connected)
    (hG : HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel G.Adj := dG
     G.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  letI : DecidableRel G.Adj := dG
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.planarDrawing_face_inequality__p2m_4d791eca_86d6_477c_bca9_50e3b58ef00f_a1
      G dG hconn hG hcard
  omega