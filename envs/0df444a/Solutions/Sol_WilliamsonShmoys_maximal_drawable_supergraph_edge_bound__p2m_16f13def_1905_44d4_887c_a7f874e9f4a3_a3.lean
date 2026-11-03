-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_supergraph_edge_bound__p2m_16f13def_1905_44d4_887c_a7f874e9f4a3_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:31:46.631991+00:00
-- url     : https://prove2.me/submissions/4d2a547e-f619-4300-8b59-9a65a7367be2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_euler_edge_count__p2m_fd50f30a_a705_4e8f_aa70_6c141aacfb17_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdraw : HasPlanarDrawingOn M)
    (hmax : forall N : SimpleGraph V,
      (forall u v, M.Adj u v -> N.Adj u v) ->
      HasPlanarDrawingOn N ->
      forall u v, N.Adj u v -> M.Adj u v) :
    letI : forall G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    3 * Fintype.card V - 6 ≤ M.edgeFinset.card := by
  classical
  have hEq := WilliamsonShmoys.maximal_drawable_graph_has_euler_edge_count__p2m_fd50f30a_a705_4e8f_aa70_6c141aacfb17_a1
    M hcard hdraw hmax
  exact le_of_eq hEq