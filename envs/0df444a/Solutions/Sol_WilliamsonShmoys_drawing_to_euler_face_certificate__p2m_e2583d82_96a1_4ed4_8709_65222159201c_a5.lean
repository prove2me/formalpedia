-- Prove2me | solution 1 for WilliamsonShmoys.drawing_to_euler_face_certificate__p2m_e2583d82_96a1_4ed4_8709_65222159201c_a5
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:33:40.346397+00:00
-- url     : https://prove2.me/submissions/2167a057-92e0-46ec-af5f-307af56be035

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_formula__p2m_6e5a9dbe_f5b6_4fde_9426_557ef9f6a091_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_from_drawing__p2m_6e5a9dbe_f5b6_4fde_9426_557ef9f6a091_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hconn : K.Connected)
    (hK : HasPlanarDrawingOn K) :
    letI : (L : SimpleGraph V) -> DecidableRel L.Adj :=
      fun L => Classical.decRel L.Adj
    ∃ f : Nat,
      Fintype.card V + f = K.edgeFinset.card + 2 ∧
      3 * f <= 2 * K.edgeFinset.card := by
  classical
  letI : (L : SimpleGraph V) -> DecidableRel L.Adj :=
    fun L => Classical.decRel L.Adj
  obtain ⟨f, heuler⟩ :=
    WilliamsonShmoys.connected_planar_drawing_euler_formula__p2m_6e5a9dbe_f5b6_4fde_9426_557ef9f6a091_a1
      K hcard hconn hK
  have hedge :=
    WilliamsonShmoys.planar_edge_bound_from_drawing__p2m_6e5a9dbe_f5b6_4fde_9426_557ef9f6a091_a1
      K hcard hconn hK
  exact ⟨f, heuler, by omega⟩