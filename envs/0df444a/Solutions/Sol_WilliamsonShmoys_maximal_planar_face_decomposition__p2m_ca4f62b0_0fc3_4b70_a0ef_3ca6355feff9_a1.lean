-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_decomposition__p2m_ca4f62b0_0fc3_4b70_a0ef_3ca6355feff9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:25:31.343659+00:00
-- url     : https://prove2.me/submissions/fcff382a-8e95-4d05-9528-ff45589cc03a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_euler_edge_bound__p2m_a3e0b5a8_b607_4050_8296_f0effeafa525_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_a3e0b5a8_b607_4050_8296_f0effeafa525_a2

set_option autoImplicit false

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f = 2 * K.edgeSet.ncard := by
  obtain ⟨f, hEuler, hUpper⟩ :=
    WilliamsonShmoys.planar_euler_edge_bound__p2m_a3e0b5a8_b607_4050_8296_f0effeafa525_a2
      K hK hmax hV
  have hLower :=
    WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_a3e0b5a8_b607_4050_8296_f0effeafa525_a2
      K hK hmax hV
  have hEdges : K.edgeSet.ncard = 3 * Fintype.card V - 6 := by omega
  exact ⟨f, hEuler, by omega⟩