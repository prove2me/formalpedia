-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion_edge_count_20261026
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:23:20.258125+00:00
-- url     : https://prove2.me/submissions/00f74c9d-5721-42ce-b048-680036cbe58f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_maximal
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_20261026_dad7fe2d8c9e421797660577ae1aff58

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V) :
    Exists fun K : SimpleGraph V =>
      And (L <= K) (And (WilliamsonShmoys.HasPlanarDrawingOn K)
        (K.edgeSet.ncard = 3 * Fintype.card V - 6)) := by
  obtain ⟨K, hLK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_maximal L hL
  exact ⟨K, hLK, hK,
    WilliamsonShmoys.maximal_planar_edge_count_20261026_dad7fe2d8c9e421797660577ae1aff58
      K hK hmax hV⟩