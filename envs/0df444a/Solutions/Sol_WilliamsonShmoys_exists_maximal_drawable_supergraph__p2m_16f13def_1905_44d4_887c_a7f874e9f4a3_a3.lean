-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_16f13def_1905_44d4_887c_a7f874e9f4a3_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:32:45.4036+00:00
-- url     : https://prove2.me/submissions/96f88c2d-233f-40d0-a894-3bef6627d4ed

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_graph_exists_maximal_predicate_supergraph__p2m_4dc84fc8_9837_496e_bb19_eb0d0139a4ff_a2
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hdraw : HasPlanarDrawingOn L) :
    letI : forall G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    exists M : SimpleGraph V,
      L.edgeFinset ⊆ M.edgeFinset /\
      HasPlanarDrawingOn M /\
      forall N : SimpleGraph V,
        (forall u v, M.Adj u v -> N.Adj u v) ->
        HasPlanarDrawingOn N ->
        forall u v, N.Adj u v -> M.Adj u v := by
  classical
  exact WilliamsonShmoys.finite_graph_exists_maximal_predicate_supergraph__p2m_4dc84fc8_9837_496e_bb19_eb0d0139a4ff_a2
    L HasPlanarDrawingOn hdraw