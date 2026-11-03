-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_data__p2m_30cffe24_7203_4ddb_9bd1_f31532d2c872_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T20:58:14.322643+00:00
-- url     : https://prove2.me/submissions/4aa061b3-7260-4959-a974-38796b89493c

import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_data__p2m_01a7d165_7651_4131_ac22_8a7ef39ee9e3_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_01a7d165_7651_4131_ac22_8a7ef39ee9e3_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (dK : DecidableRel K.Adj) (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V) :
    ∃ f l : Nat, Fintype.card V + f = K.edgeFinset.card + 2 ∧
      3 * f <= l ∧ l = 2 * K.edgeFinset.card := by
  letI : DecidableRel K.Adj := dK
  obtain ⟨f, l, hEuler, hIncidence⟩ :=
    WilliamsonShmoys.planar_drawing_euler_data__p2m_01a7d165_7651_4131_ac22_8a7ef39ee9e3_a1
      K dK hconn hK
  have hEdgeBound :=
    WilliamsonShmoys.planar_drawing_edge_bound__p2m_01a7d165_7651_4131_ac22_8a7ef39ee9e3_a1
      K dK hconn hK hcard
  exact ⟨f, l, hEuler, by omega, hIncidence⟩