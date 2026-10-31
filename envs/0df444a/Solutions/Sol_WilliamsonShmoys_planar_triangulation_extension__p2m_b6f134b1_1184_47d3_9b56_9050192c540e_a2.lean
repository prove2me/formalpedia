-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_b6f134b1_1184_47d3_9b56_9050192c540e_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:03:04.407488+00:00
-- url     : https://prove2.me/submissions/780046cd-6d0f-48e5-a579-b8a6ba02eb27

import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_has_triangulated_extension

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hCard : 3 <= Fintype.card V) :
    ∃ U : SimpleGraph V, T ≤ U ∧
      WilliamsonShmoys.HasPlanarDrawingOn U ∧
      U.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawingOn_has_triangulated_extension T hDraw hCard
