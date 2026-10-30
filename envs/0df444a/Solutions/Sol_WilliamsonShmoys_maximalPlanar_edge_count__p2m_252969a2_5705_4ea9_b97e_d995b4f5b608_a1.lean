-- Prove2me | solution 1 for WilliamsonShmoys.maximalPlanar_edge_count__p2m_252969a2_5705_4ea9_b97e_d995b4f5b608_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:19:36.695493+00:00
-- url     : https://prove2.me/submissions/a84149ee-faf6-4c2f-a897-691a4c49fbab
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition__p2m_7a0d3f25_089a_4d82_a9d5_85ef68cd5f10_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N = M)
    (hV : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨f, hEuler, hIncidence⟩ :=
    WilliamsonShmoys.maximal_planar_face_decomposition__p2m_7a0d3f25_089a_4d82_a9d5_85ef68cd5f10_a1
      M hDraw hMax hV
  omega