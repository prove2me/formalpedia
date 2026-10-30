-- Prove2me | solution 1 for WilliamsonShmoys.euler_compatible_face_count_incidence_7c1cdf82
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T13:31:03.126051+00:00
-- url     : https://prove2.me/submissions/859faf54-7772-4593-9f14-e9729475b26a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_euler_face_count_planar_edge_bound_4d0c2802_8f3b_4d79_b31d_d0704c9c8543

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hcard : 3 ≤ Fintype.card V)
    (f : Nat)
    (heuler : Fintype.card V + f = H.edgeSet.ncard + 2) :
    3 * f ≤ 2 * H.edgeSet.ncard := by
  have hedge := WilliamsonShmoys.euler_face_count_planar_edge_bound_4d0c2802_8f3b_4d79_b31d_d0704c9c8543 H hH hconn hcard
  omega