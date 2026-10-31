-- Prove2me | solution 2 for WilliamsonShmoys.planar_triangulated_extension__p2m_30f04ba5_7c4d_43f6_bbf4_fbaceb7763c4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:03:07.475726+00:00
-- url     : https://prove2.me/submissions/4e6d3bd0-43aa-4bc8-81ce-379509dd29bd

import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_has_triangulated_extension

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawingOn_has_triangulated_extension L hDraw hCard
