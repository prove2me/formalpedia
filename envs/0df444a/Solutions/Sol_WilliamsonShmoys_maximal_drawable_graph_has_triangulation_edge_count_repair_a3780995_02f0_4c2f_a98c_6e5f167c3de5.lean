-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_has_triangulation_edge_count_repair_a3780995_02f0_4c2f_a98c_6e5f167c3de5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T11:59:43.717266+00:00
-- url     : https://prove2.me/submissions/5c0ab745-e809-4c3d-9d5b-ae1e8dbdfdeb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_planar_edge_upper_bound
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_planar_edge_lower_bound

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (hPdraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ Q : SimpleGraph V,
      P ≤ Q → WilliamsonShmoys.HasPlanarDrawingOn Q → Q = P) :
    P.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hup := WilliamsonShmoys.maximal_drawable_graph_planar_edge_upper_bound
    P hPdraw hCard
  have hlo := WilliamsonShmoys.maximal_drawable_graph_planar_edge_lower_bound
    P hPdraw hCard hmax
  omega
