-- Prove2me | solution 1 for WilliamsonShmoys_edge_count_of_maximal_planar_supergraph__p2m_a21b9daf_96c0_42bf_b053_e1966758807a_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:31:15.009923+00:00
-- url     : https://prove2.me/submissions/3c3e673f-4fbb-434b-8f94-dd71591e4eec
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_count__p2m_6bb0623d_4ea1_4aa8_a0da_a55490a47412_a2
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hconn : H.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     H.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  classical
  obtain ⟨f, hEuler, hIncidence⟩ :=
    WilliamsonShmoys.maximal_planar_face_count__p2m_6bb0623d_4ea1_4aa8_a0da_a55490a47412_a2
      H hcard hconn hdraw hmax
  omega