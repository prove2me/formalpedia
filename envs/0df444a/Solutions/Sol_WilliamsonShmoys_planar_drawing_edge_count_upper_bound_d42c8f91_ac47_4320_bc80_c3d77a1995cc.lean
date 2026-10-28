-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_upper_bound_d42c8f91_ac47_4320_bc80_c3d77a1995cc
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:24:15.970361+00:00
-- url     : https://prove2.me/submissions/2fb74742-0455-4fb5-afc5-ee0fbed84157
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension_d42c8f91_ac47_4320_bc80_c3d77a1995cc
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_d42c8f91_ac47_4320_bc80_c3d77a1995cc
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono_d42c8f91_ac47_4320_bc80_c3d77a1995cc

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    M.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨H, hMH, hPlanar, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_extension_d42c8f91_ac47_4320_bc80_c3d77a1995cc
      M hV hM
  have hCount :=
    WilliamsonShmoys.maximal_planar_edge_count_d42c8f91_ac47_4320_bc80_c3d77a1995cc
      H hV hPlanar hMax
  have hMono :=
    WilliamsonShmoys.edgeSet_ncard_mono_d42c8f91_ac47_4320_bc80_c3d77a1995cc
      M H hMH
  omega