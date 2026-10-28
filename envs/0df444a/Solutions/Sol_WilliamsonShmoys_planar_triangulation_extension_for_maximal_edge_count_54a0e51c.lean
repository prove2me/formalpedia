-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension_for_maximal_edge_count_54a0e51c
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T11:53:20.004554+00:00
-- url     : https://prove2.me/submissions/fe7d4df9-198b-4864-9be7-3c77b7d615e2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_for_edge_count_54a0e51c
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_extension_54a0e51c

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hL, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_for_edge_count_54a0e51c K hK
  have hCount :=
    WilliamsonShmoys.maximal_planar_edge_count_for_extension_54a0e51c L hL hV hMax
  exact ⟨L, hKL, hL, hCount⟩
