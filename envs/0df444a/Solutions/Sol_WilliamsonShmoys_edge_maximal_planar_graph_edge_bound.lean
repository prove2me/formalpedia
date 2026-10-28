-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_graph_edge_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:43:30.864992+00:00
-- url     : https://prove2.me/submissions/5c155a0a-8643-4b30-9eeb-046891b351f6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_extension_edge_bound

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : forall N : SimpleGraph V, M <= N ->
      WilliamsonShmoys.HasPlanarDrawingOn N -> N <= M) :
    3 * Fintype.card V <= M.edgeSet.ncard + 6 := by
  obtain ⟨N, hMN, hNplanar, hNbound⟩ :=
    WilliamsonShmoys.planar_maximal_extension_edge_bound M hV hM
  have hNM : N <= M := hmax N hMN hNplanar
  have hcard : N.edgeSet.ncard <= M.edgeSet.ncard :=
    Set.ncard_mono (SimpleGraph.edgeSet_mono hNM)
  omega