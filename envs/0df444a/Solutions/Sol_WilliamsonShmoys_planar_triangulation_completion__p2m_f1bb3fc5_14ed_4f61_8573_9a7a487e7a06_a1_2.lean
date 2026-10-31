-- Prove2me | solution 2 for WilliamsonShmoys.planar_triangulation_completion__p2m_f1bb3fc5_14ed_4f61_8573_9a7a487e7a06_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:28:04.559209+00:00
-- url     : https://prove2.me/submissions/2550b561-ade7-4d3c-9946-e041ceb65572

import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_exact_edge_count_completion__p2m_59c448d8_2415_4b81_b96a_4b978426d513_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) : ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ 3 * Fintype.card V - 6 = L.edgeSet.ncard :=
  WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_59c448d8_2415_4b81_b96a_4b978426d513_a1 K hK hV
