-- Prove2me | solution 1 for WilliamsonShmoys.planarEulerData_edgeBound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T17:27:48.395757+00:00
-- url     : https://prove2.me/submissions/efd02480-9f9a-453e-8f10-de5b4f302f7e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_PlanarEulerData

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (data : WilliamsonShmoys.PlanarEulerData G)
    (hV : 3 <= Fintype.card V) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  have hEuler := data.euler
  have hBoundary := data.faceBoundary
  have hInt : (G.edgeSet.ncard : ℤ) + 6 <=
      3 * (Fintype.card V : ℤ) := by
    omega
  exact_mod_cast hInt