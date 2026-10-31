-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_face_count__p2m_46140569_4e36_49c3_b704_27def16a2d74_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:31:21.542188+00:00
-- url     : https://prove2.me/submissions/4118834e-157d-4db2-ae35-87bb7eee1ba5

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_euler_face_count__p2m_714e0d6d_4b4e_4713_bad3_a0723dae3971_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_714e0d6d_4b4e_4713_bad3_a0723dae3971_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn H)
    (hconnected : H.Connected)
    (hV : 3 <= Fintype.card V) :
    ∃ F : ℕ,
      Fintype.card V + F = H.edgeSet.ncard + 2 ∧
      3 * F <= 2 * H.edgeSet.ncard := by
  obtain ⟨F, hEuler⟩ :=
    WilliamsonShmoys.euler_face_count__p2m_714e0d6d_4b4e_4713_bad3_a0723dae3971_a1
      H hplanar hconnected
  have hEdges :=
    WilliamsonShmoys.planar_edge_bound__p2m_714e0d6d_4b4e_4713_bad3_a0723dae3971_a1
      H hplanar hconnected hV
  refine ⟨F, hEuler, ?_⟩
  omega