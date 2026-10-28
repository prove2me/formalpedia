-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count_upper_bound_repair_8fa97b2b
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:53:00.70299+00:00
-- url     : https://prove2.me/submissions/2659a71a-f0a8-41f9-944b-88f0b911ba03
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_repair_8fa97b2b
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_repair_8fa97b2b

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hMH, hHd, hHmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_repair_8fa97b2b M hM
  calc
    M.edgeSet.ncard ≤ H.edgeSet.ncard := Set.ncard_mono hMH
    _ ≤ 3 * Fintype.card V - 6 :=
      WilliamsonShmoys.maximal_planar_edge_count_repair_8fa97b2b
        H hV hHd hHmax