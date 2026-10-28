-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_with_deficient_edge_count_has_proper_drawable_extension_b5197173
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T10:48:50.4951+00:00
-- url     : https://prove2.me/submissions/bab6a826-8940-47e1-bc5a-7a049c9efce9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_b5197173
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_lower_bound_b5197173

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcount : M.edgeSet.ncard < 3 * Fintype.card V - 6) :
    Exists (fun N : SimpleGraph V =>
      And (M <= N)
        (And (Not (N = M)) (WilliamsonShmoys.HasPlanarDrawingOn N))) := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph_b5197173 M hM
  have hbound :=
    WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound_b5197173 N hV hN hmax
  refine ⟨N, hMN, ?_, hN⟩
  intro hEq
  subst N
  omega