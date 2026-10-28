-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_supergraph_exists_20261026
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:44:12.008958+00:00
-- url     : https://prove2.me/submissions/c9a0f314-5442-4d20-993a-24a53385f8e5

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_supergraph_maximal

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ K' : SimpleGraph V,
      K ≤ K' ∧ WilliamsonShmoys.HasPlanarDrawingOn K' ∧
        ∀ L : SimpleGraph V,
          K' ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K' := by
  classical
  exact finite_supergraph_maximal K WilliamsonShmoys.HasPlanarDrawingOn hK