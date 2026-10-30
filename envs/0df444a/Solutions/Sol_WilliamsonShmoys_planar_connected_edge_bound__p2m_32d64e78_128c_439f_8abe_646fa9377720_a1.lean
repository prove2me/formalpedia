-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_edge_bound__p2m_32d64e78_128c_439f_8abe_646fa9377720_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:12:48.635989+00:00
-- url     : https://prove2.me/submissions/46e25329-b555-4915-938c-35ad13543fe9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_face_degree_data_of_drawing__p2m_b3c6b6cb_4e1e_4bbd_a7fa_10f7493b8310_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hV : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨m, degree, hEuler, hsum, hdegree⟩ :=
    WilliamsonShmoys.planar_face_degree_data_of_drawing__p2m_b3c6b6cb_4e1e_4bbd_a7fa_10f7493b8310_a2
      H hH hconn hV
  have hconstant :
      3 * m = ∑ f : Fin m, (3 : Nat) := by
    simp [Nat.mul_comm]
  have hlower : 3 * m ≤ ∑ f : Fin m, degree f := by
    rw [hconstant]
    exact Finset.sum_le_sum (fun f _ => hdegree f)
  rw [hsum] at hlower
  omega