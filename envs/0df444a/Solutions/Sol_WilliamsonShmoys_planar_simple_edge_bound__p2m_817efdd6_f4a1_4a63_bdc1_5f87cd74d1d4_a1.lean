-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_edge_bound__p2m_817efdd6_f4a1_4a63_bdc1_5f87cd74d1d4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:53:44.732592+00:00
-- url     : https://prove2.me/submissions/ba041786-e427-44ab-87c3-bce45dbf856d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_boundary_count__p2m_e743f516_2fe6_4f90_ae81_e51127ac517d_a3
import Theorems.Thm_WilliamsonShmoys_planar_face_count_edge_bound__p2m_e743f516_2fe6_4f90_ae81_e51127ac517d_a3

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) (hconn : M.Connected)
    (hcard : Nat.le 3 (Fintype.card V)) :
    Nat.le (M.edgeFinset.card + 6) (3 * Fintype.card V) := by
  refine Exists.elim
    (WilliamsonShmoys.planar_drawing_face_boundary_count__p2m_e743f516_2fe6_4f90_ae81_e51127ac517d_a3
      M hM hconn hcard) ?_
  intro lengths hdata
  exact WilliamsonShmoys.planar_face_count_edge_bound__p2m_e743f516_2fe6_4f90_ae81_e51127ac517d_a3
    (Fintype.card V) M.edgeFinset.card lengths hcard
    hdata.left hdata.right.left hdata.right.right
