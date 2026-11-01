-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_4f0f4017_69c8_49f6_a405_0b1a215ecea7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:56:03.27923+00:00
-- url     : https://prove2.me/submissions/63c28c43-1578-4657-a831-3c05ac4ec6ee

import Theorems.Thm_exists_maximal_simpleGraph_extension__p2m_87ed5adb_82f3_488c_b808_7f2da9357c21_a1
import Mathlib

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hconn : L.Connected) :
    ∃ H : SimpleGraph V, L ≤ H ∧ H.Connected ∧
      HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H := by
  obtain ⟨H, hLH, hPlanar, hmax⟩ :=
    exists_maximal_simpleGraph_extension__p2m_87ed5adb_82f3_488c_b808_7f2da9357c21_a1
      L HasPlanarDrawingOn hL
  refine ⟨H, hLH, SimpleGraph.Connected.mono hLH hconn, hPlanar, ?_⟩
  intro K hHK hK
  exact hmax K hHK hK