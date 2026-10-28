-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_edge_count_euler_upper_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T10:48:31.214892+00:00
-- url     : https://prove2.me/submissions/0d7f3436-4de7-44e2-b223-274ff3ce8269
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_connected_planar_supergraph_edge_count
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_bound

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn X)
    (hCard : 3 ≤ Fintype.card V) :
    X.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨Y, hmono, hconn, hYdraw⟩ :=
    WilliamsonShmoys.exists_connected_planar_supergraph_edge_count X hdraw hCard
  have hY := WilliamsonShmoys.connected_planar_edge_count_bound Y hYdraw hCard hconn
  omega