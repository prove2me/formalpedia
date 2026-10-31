-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_count_upper_bound__p2m_517acab8_1dff_430a_88ba_b65381dc6f37_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:01:12.796831+00:00
-- url     : https://prove2.me/submissions/85e51cab-e003-40ce-a7e9-8f304358481c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_3c187467_059b_4073_9a0b_83e3bfc104a1_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_eq__p2m_3c187467_059b_4073_9a0b_83e3bfc104a1_a1
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (Z : SimpleGraph V) (hconn : Z.Connected) (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z) (hV : 3 ≤ Fintype.card V) : Z.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hZH, hcard, hdraw, hmax⟩ := WilliamsonShmoys.maximal_planar_extension__p2m_3c187467_059b_4073_9a0b_83e3bfc104a1_a1 Z hZ
  have hEq := WilliamsonShmoys.maximal_planar_edge_count_eq__p2m_3c187467_059b_4073_9a0b_83e3bfc104a1_a1 H hdraw hV hmax
  exact hcard.trans (le_of_eq hEq)