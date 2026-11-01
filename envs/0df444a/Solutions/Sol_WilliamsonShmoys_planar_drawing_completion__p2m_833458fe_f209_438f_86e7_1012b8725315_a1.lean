-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_completion__p2m_833458fe_f209_438f_86e7_1012b8725315_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:51:52.690067+00:00
-- url     : https://prove2.me/submissions/c379a496-a870-4646-9708-2fd9417bdef1

import Theorems.Thm_finite_graph_maximal_extension__p2m_631bc0f5_f3dc_4eb9_811c_fa1521bf437a_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hcard : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V,
      (∀ u v, H.Adj u v → K.Adj u v) ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard ∧
      HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V, HasPlanarDrawingOn L →
        (∀ u v, K.Adj u v → L.Adj u v) → L = K) := by
  exact finite_graph_maximal_extension__p2m_631bc0f5_f3dc_4eb9_811c_fa1521bf437a_a1
    (P := HasPlanarDrawingOn) H hH