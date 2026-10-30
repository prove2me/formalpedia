-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound_from_embedding
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T10:32:31.831622+00:00
-- url     : https://prove2.me/submissions/86e91b84-ff7e-4e32-83a9-36755d3f4105

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card
import Theorems.Thm_WilliamsonShmoys_exists_triangulated_planar_supergraph_for_drawing_edge_bound

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hMdraw : WilliamsonShmoys.HasPlanarDrawingOn M) :
    M.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨H, hsub, hHdraw, hHcard⟩ :=
    WilliamsonShmoys.exists_triangulated_planar_supergraph_for_drawing_edge_bound
      M hV hMdraw
  have hle : M.edgeSet.ncard <= H.edgeSet.ncard := Set.ncard_mono hsub
  omega