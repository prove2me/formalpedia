-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_edge_count_lower
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T23:13:46.057009+00:00
-- url     : https://prove2.me/submissions/5993e030-00d6-4bff-b5a0-10a7c71ea1a7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_drawable_79011c86fe2a4d17
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_79011c86fe2a4d17

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hT : HasPlanarDrawingOn T) :
    ∃ U : SimpleGraph V, T ≤ U ∧ HasPlanarDrawingOn U ∧
      3 * Fintype.card V ≤ U.edgeSet.ncard + 6 := by
  obtain ⟨U, hTU, hU, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_maximal_drawable_79011c86fe2a4d17 T hT
  exact ⟨U, hTU, hU,
    WilliamsonShmoys.maximal_planar_edge_count_lower_79011c86fe2a4d17 U hV hU hmax⟩