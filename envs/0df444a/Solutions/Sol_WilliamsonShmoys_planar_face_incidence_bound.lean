-- Prove2me | solution 1 for WilliamsonShmoys.planar_face_incidence_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T11:55:02.013688+00:00
-- url     : https://prove2.me/submissions/a644f96a-1bec-4603-bc11-c01275adf122
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_face_incidence_bound_edge_bound_fd674c06_a657_4ca8_b75f_41f75c897817

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hconn : K.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    ∀ F : ℕ, Fintype.card V + F = K.edgeSet.ncard + 2 →
      3 * F <= 2 * K.edgeSet.ncard := by
  intro F hEuler
  have hEdge := WilliamsonShmoys.planar_face_incidence_bound_edge_bound_fd674c06_a657_4ca8_b75f_41f75c897817
    K hconn hdraw hV
  omega