-- Prove2me | solution 1 for WilliamsonShmoys_maximal_planar_triangular_face_incidence__p2m_a5abbcfc_8844_40a4_806c_eef213b4f62c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:56:21.881291+00:00
-- url     : https://prove2.me/submissions/a3ade545-4f56-4062-9608-1a6aa2072836

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_3a65eae3_5ff7_4fce_93d5_4a7db05ee858_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H)
    (hHplanar : HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H)
    (hV : 3 ≤ Fintype.card V)
    (hconn : H.Connected)
    (f : ℕ)
    (hEuler : Fintype.card V + f = H.edgeSet.ncard + 2) :
    2 * H.edgeSet.ncard = 3 * f := by
  have hEdges := WilliamsonShmoys_maximal_planar_edge_count__p2m_3a65eae3_5ff7_4fce_93d5_4a7db05ee858_a1
    H hHplanar hmax hV hconn
  omega