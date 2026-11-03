-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_incidence__p2m_e77a557c_0981_440f_93d6_d7c4c9434599_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:40:46.191646+00:00
-- url     : https://prove2.me/submissions/02369320-05da-4ea7-acd5-826e6f197e24

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_61dc9438_8340_4e4c_b1c7_250f3c9d3d5d_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hK : HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V, K <= L -> HasPlanarDrawingOn L -> L <= K)
    (f : Nat) (heuler : Fintype.card V + f = K.edgeSet.ncard + 2) :
    3 * f = 2 * K.edgeSet.ncard := by
  have hedge := WilliamsonShmoys.maximal_planar_edge_count__p2m_61dc9438_8340_4e4c_b1c7_250f3c9d3d5d_a1
    K hcard hK hmax
  omega