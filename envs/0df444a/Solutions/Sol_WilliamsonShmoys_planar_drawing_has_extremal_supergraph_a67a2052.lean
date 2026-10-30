-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_extremal_supergraph_a67a2052
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T12:56:12.034015+00:00
-- url     : https://prove2.me/submissions/b304dd18-82d8-4175-af21-00cc84697878

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_edge_maximal_supergraph
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_graph_has_extremal_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hX : HasPlanarDrawingOn X)
    (hCard : 3 <= Fintype.card V) :
    exists Y : SimpleGraph V,
      HasPlanarDrawingOn Y /\
      (forall u v, X.Adj u v -> Y.Adj u v) /\
      Y.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨Y, hY, hXY, hMax⟩ :=
    WilliamsonShmoys.planar_graph_has_edge_maximal_supergraph X hX
  refine ⟨Y, hY, hXY, ?_⟩
  exact WilliamsonShmoys.edge_maximal_planar_graph_has_extremal_edge_count
    Y hY hMax hCard