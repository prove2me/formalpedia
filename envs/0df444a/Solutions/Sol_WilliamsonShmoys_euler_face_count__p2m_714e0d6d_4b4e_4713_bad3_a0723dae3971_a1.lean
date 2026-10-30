-- Prove2me | solution 1 for WilliamsonShmoys.euler_face_count__p2m_714e0d6d_4b4e_4713_bad3_a0723dae3971_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:38:59.611978+00:00
-- url     : https://prove2.me/submissions/e7c6d914-89ae-42dd-a66f-1dc7f2ac6d37

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_spanning_tree_card__p2m_1954d530_c7a1_4324_8033_8836e3ec1363_a1
import Theorems.Thm_WilliamsonShmoys_euler_from_spanning_tree__p2m_1954d530_c7a1_4324_8033_8836e3ec1363_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn H)
    (hconnected : H.Connected) :
    ∃ F : ℕ, Fintype.card V + F = H.edgeSet.ncard + 2 := by
  obtain hzero | ⟨T, hsub, hTconnected, hTcard⟩ :=
    WilliamsonShmoys.connected_spanning_tree_card__p2m_1954d530_c7a1_4324_8033_8836e3ec1363_a1
      H hconnected
  · obtain ⟨hVzero, hEzero⟩ := hzero
    exact ⟨2, by omega⟩
  · exact WilliamsonShmoys.euler_from_spanning_tree__p2m_1954d530_c7a1_4324_8033_8836e3ec1363_a1
      H T hplanar hconnected hsub hTconnected hTcard