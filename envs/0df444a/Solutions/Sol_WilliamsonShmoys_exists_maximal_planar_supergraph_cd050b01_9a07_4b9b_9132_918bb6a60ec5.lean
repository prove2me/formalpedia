-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph_cd050b01_9a07_4b9b_9132_918bb6a60ec5
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:15:03.239008+00:00
-- url     : https://prove2.me/submissions/5eca042c-0c06-4294-9b37-f71db2364c3f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_simplegraph_extension

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R) :
    ∃ H : SimpleGraph V,
      R ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) := by
  exact WilliamsonShmoys.finite_maximal_simplegraph_extension
    R WilliamsonShmoys.HasPlanarDrawingOn hR