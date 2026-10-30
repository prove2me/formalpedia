-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T23:49:19.029365+00:00
-- url     : https://prove2.me/submissions/fc048c33-7692-4899-8490-4d0024525f40

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_bound
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_mono

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hMH, hH, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension M hM hV
  exact (WilliamsonShmoys.planar_edge_count_mono M H hMH).trans
    (WilliamsonShmoys.maximal_planar_drawing_edge_bound H hH hV hmax)