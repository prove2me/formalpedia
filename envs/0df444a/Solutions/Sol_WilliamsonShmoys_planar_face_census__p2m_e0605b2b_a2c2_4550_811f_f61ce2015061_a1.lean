-- Prove2me | solution 1 for WilliamsonShmoys.planar_face_census__p2m_e0605b2b_a2c2_4550_811f_f61ce2015061_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:25:49.37199+00:00
-- url     : https://prove2.me/submissions/70a4cd4d-4ab8-46ec-8821-af3d9c9f60f7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_euler__p2m_2343a1b4_cbe5_4a48_b836_711e4285cb1c_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_2343a1b4_cbe5_4a48_b836_711e4285cb1c_a1
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn H)
    (hconnected : H.Connected)
    (hV : 3 <= Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = H.edgeSet.ncard + 2 ∧
      3 * f <= 2 * H.edgeSet.ncard := by
  obtain ⟨f, heuler⟩ :=
    WilliamsonShmoys.connected_planar_euler__p2m_2343a1b4_cbe5_4a48_b836_711e4285cb1c_a1
      H hplanar hconnected
  have hbound :=
    WilliamsonShmoys.planar_edge_bound__p2m_2343a1b4_cbe5_4a48_b836_711e4285cb1c_a1
      H hplanar hV
  refine ⟨f, heuler, ?_⟩
  omega