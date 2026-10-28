-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T08:43:57.419373+00:00
-- url     : https://prove2.me/submissions/b6028c45-4299-4955-9af0-e4e918da5c24
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_supergraph_1176f3f1_fbd8_4a0d_b66b_36bdd6543cc3

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : HasPlanarDrawingOn G)
    (hmax : forall M : SimpleGraph V,
      Set.Subset G.edgeSet M.edgeSet ->
      HasPlanarDrawingOn M -> M.edgeSet = G.edgeSet) :
    3 * Fintype.card V - 6 <= G.edgeSet.ncard := by
  cases WilliamsonShmoys.exists_planar_triangulation_supergraph_1176f3f1_fbd8_4a0d_b66b_36bdd6543cc3 G hV hG with
  | intro H hrest =>
    cases hrest with
    | intro hsub hrest =>
      cases hrest with
      | intro hH hcount =>
        have heq := hmax H hsub hH
        have hbound : 3 * Fintype.card V - 6 <= H.edgeSet.ncard := by omega
        simpa [heq] using hbound