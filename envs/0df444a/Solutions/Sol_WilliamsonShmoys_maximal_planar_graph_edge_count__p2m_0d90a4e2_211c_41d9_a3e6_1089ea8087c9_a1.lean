-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_0d90a4e2_211c_41d9_a3e6_1089ea8087c9_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:58:07.788884+00:00
-- url     : https://prove2.me/submissions/109d380b-0490-4ef3-8a7c-b7927f8d9120
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_triangle_count__p2m_2a0eb6c3_e8b8_46c5_bb28_c648f00dcb7f_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hK : HasPlanarDrawingOn K)
    (hmax : ∀ H : SimpleGraph V, K ≤ H → HasPlanarDrawingOn H → H ≤ K) :
    3 * Fintype.card V = K.edgeSet.ncard + 6 := by
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.maximal_planar_euler_triangle_count__p2m_2a0eb6c3_e8b8_46c5_bb28_c648f00dcb7f_a1
      K hV hK hmax
  omega