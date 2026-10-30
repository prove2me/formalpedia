-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_edge_bound__p2m_971f615d_fe0b_4924_8df8_81bd7d133755_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:26:53.10986+00:00
-- url     : https://prove2.me/submissions/e0c06403-ca20-454f-840f-1eeadff4c45f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition__p2m_ca4f62b0_0fc3_4b70_a0ef_3ca6355feff9_a1

set_option autoImplicit false

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  obtain ⟨f, hEuler, hIncidence⟩ :=
    WilliamsonShmoys.maximal_planar_face_decomposition__p2m_ca4f62b0_0fc3_4b70_a0ef_3ca6355feff9_a1
      K hK hmax hV
  omega