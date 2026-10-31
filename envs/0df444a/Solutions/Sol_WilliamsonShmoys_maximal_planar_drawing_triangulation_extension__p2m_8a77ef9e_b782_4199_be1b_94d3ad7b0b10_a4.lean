-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_triangulation_extension__p2m_8a77ef9e_b782_4199_be1b_94d3ad7b0b10_a4
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:49:11.017954+00:00
-- url     : https://prove2.me/submissions/26649291-8ce6-42a0-b419-d0a27c794a26

import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_has_triangulated_extension

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawingOn_has_triangulated_extension L hL hCard
