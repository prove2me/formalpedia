-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_below_edge_bound_can_be_augmented
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T09:13:49.916922+00:00
-- url     : https://prove2.me/submissions/e41a181c-1513-4ad0-857b-161026989287
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_extension_e6494b82
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_e6494b82

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hSmall : L.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧ M ≠ L := by
  obtain ⟨M, hLM, hM, hMax⟩ :=
    WilliamsonShmoys.planar_supergraph_maximal_extension_e6494b82 L hL
  have hEdges :=
    WilliamsonShmoys.maximal_planar_edge_count_e6494b82 M hM hCard hMax
  refine ⟨M, hLM, hM, ?_⟩
  intro hEq
  subst M
  omega