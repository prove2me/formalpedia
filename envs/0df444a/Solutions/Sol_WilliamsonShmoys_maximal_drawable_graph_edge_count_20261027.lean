-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count_20261027
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T20:07:25.84699+00:00
-- url     : https://prove2.me/submissions/9da57e3e-fd57-42b9-b49e-849bd4b9e6c0

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_drawable_edge_count_upper_bound_20261027
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_lower_bound_20261027

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hGplanar : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hGmax : forall K : SimpleGraph V, G.edgeSet ⊆ K.edgeSet ->
      WilliamsonShmoys.HasPlanarDrawingOn K -> K.edgeSet ⊆ G.edgeSet) :
    G.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper :=
    WilliamsonShmoys.planar_simple_drawable_edge_count_upper_bound_20261027
      G hV hGplanar
  have hlower :=
    WilliamsonShmoys.maximal_drawable_edge_count_lower_bound_20261027
      G hV hGplanar hGmax
  omega