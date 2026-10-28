-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_d42c8f91_ac47_4320_bc80_c3d77a1995cc
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:42:34.970627+00:00
-- url     : https://prove2.me/submissions/63a2447c-eb85-4a2f-a5c0-8baa2c52e088
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulated_completion_d42c8f91_ac47_4320_bc80_c3d77a1995cc

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hCount⟩ :=
    WilliamsonShmoys.planar_triangulated_completion_d42c8f91_ac47_4320_bc80_c3d77a1995cc H hV hH
  have hKH : K = H := hMax K hHK hK
  simpa [hKH] using hCount