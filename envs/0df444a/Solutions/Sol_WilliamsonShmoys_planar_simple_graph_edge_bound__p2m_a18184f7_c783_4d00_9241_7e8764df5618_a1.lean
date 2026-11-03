-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_a18184f7_c783_4d00_9241_7e8764df5618_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:00:17.274921+00:00
-- url     : https://prove2.me/submissions/c958822c-284c-447c-b1ce-163ec8db9d08

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_face_count_arithmetic__p2m_98ef7ab8_2597_47ef_b994_1be56f6b94b5_a6
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count_data__p2m_98ef7ab8_2597_47ef_b994_1be56f6b94b5_a6

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hconn : M.Connected)
    (hcard : 3 <= Fintype.card V) :
    (M.edgeFinset.card : Int) <= 3 * (Fintype.card V : Int) - 6 := by
  let n : Nat := Fintype.card V
  let m : Nat := M.edgeFinset.card
  have hn : 3 <= n := by simpa [n] using hcard
  have hdata : Exists fun f : Nat => n + f = m + 2 /\ 3 * f <= 2 * m :=
    planar_drawing_face_count_data__p2m_98ef7ab8_2597_47ef_b994_1be56f6b94b5_a6 M hM hconn hn
  have hbound :=
    planar_face_count_arithmetic__p2m_98ef7ab8_2597_47ef_b994_1be56f6b94b5_a6 hdata hn
  simpa [n, m] using hbound