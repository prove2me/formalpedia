-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_augment_edge_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T03:29:02.152748+00:00
-- url     : https://prove2.me/submissions/abcc8ce1-7cf5-4d1f-ac92-faaa3ab55719
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_maximal_extension_d11b870bf6364341
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_d11b870bf6364341

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hCard : 3 <= Fintype.card V) :
    Exists fun N : SimpleGraph V =>
      M <= N /\ HasPlanarDrawingOn N /\
      3 * Fintype.card V <= N.edgeSet.ncard + 6 := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.planar_graph_maximal_extension_d11b870bf6364341 M hM
  have hcount :=
    WilliamsonShmoys.maximal_planar_graph_edge_count_d11b870bf6364341
      N hN hCard hmax
  exact ⟨N, hMN, hN, le_of_eq hcount.symm⟩