-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_completion_edge_count_e5a7f9d6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T09:31:58.615284+00:00
-- url     : https://prove2.me/submissions/55c403f5-c111-4614-a5d1-e63895cd2923
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_e5a7f9d6
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_e5a7f9d6
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V) :
    ∃ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L ∧ K ≤ L ∧
        (L.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨L, hL, hKL, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph_e5a7f9d6 K hK
  exact ⟨L, hL, hKL,
    WilliamsonShmoys.maximal_planar_edge_count_e5a7f9d6 L hL hCard hmax⟩