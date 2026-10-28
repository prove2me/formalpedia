-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_edge_count_extension_54a0e51c
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T12:50:55.048701+00:00
-- url     : https://prove2.me/submissions/0fbb918a-5b3e-474a-8353-f74b0e5ffb74
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_54a0e51c
import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_supergraph_54a0e51c

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V) :
    Exists fun M : SimpleGraph V =>
      L.edgeSet ⊆ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_54a0e51c L hL
  refine ⟨M, hLM, hM, ?_⟩
  exact WilliamsonShmoys.edge_count_of_maximal_planar_supergraph_54a0e51c
    L M hL hV hLM hM hmax