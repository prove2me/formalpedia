-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_drawable_strict_extension__p2m_638cd013_f422_4f43_912d_3f97f91e2a69_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:31:17.064082+00:00
-- url     : https://prove2.me/submissions/cbefa02a-ba71-4cea-961e-a430e435ee86
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_vertices_unreachable__p2m_5393d3db_4535_4872_a14a_1f35d96c3cd8_a2
import Theorems.Thm_WilliamsonShmoys_planar_drawing_unreachable_edge_extension__p2m_5393d3db_4535_4872_a14a_1f35d96c3cd8_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hDisc : ¬ M.Connected) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ N ≠ M ∧ HasPlanarDrawingOn N := by
  obtain ⟨u, v, huv, hUnreachable⟩ :=
    WilliamsonShmoys.disconnected_vertices_unreachable__p2m_5393d3db_4535_4872_a14a_1f35d96c3cd8_a2
      M hV hDisc
  exact WilliamsonShmoys.planar_drawing_unreachable_edge_extension__p2m_5393d3db_4535_4872_a14a_1f35d96c3cd8_a2
    M hM u v huv hUnreachable