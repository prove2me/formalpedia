-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_upper_bound_connected__p2m_14c57b1a_9d57_45d2_8a0d_6125974ddbe0_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:34:06.564208+00:00
-- url     : https://prove2.me/submissions/559e6f7c-d07e-49bc-8524-f05c93abcda6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_eulerFaceCertificate__p2m_266245c2_b2f6_423f_b90e_ce482fe57e00_a2
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hconn : L.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨F, degree, hEuler, hDegreeSum, hDegree⟩ :=
    WilliamsonShmoys.planarDrawingOn_eulerFaceCertificate__p2m_266245c2_b2f6_423f_b90e_ce482fe57e00_a2
      L hL hconn hcard
  have hLower : 3 * F ≤ ∑ f : Fin F, degree f := by
    calc
      3 * F = ∑ _f : Fin F, 3 := by simp [Nat.mul_comm]
      _ ≤ ∑ f : Fin F, degree f :=
        Finset.sum_le_sum (fun f _ => hDegree f)
  omega