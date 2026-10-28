-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_simple_graph_triangulation_maximal_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:09:15.937356+00:00
-- url     : https://prove2.me/submissions/896a3ecb-eee7-465b-95b8-12df2c568d9d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_simpleGraph_supergraph_maximal_for_predicate

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : ∀ u v, Relation.ReflTransGen G.Adj u v)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ u v, Relation.ReflTransGen H.Adj u v) ∧
      (∀ K : SimpleGraph V, H ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K → K = H) := by
  obtain ⟨H, hGH, hH, hmax⟩ :=
    finite_simpleGraph_supergraph_maximal_for_predicate G
      WilliamsonShmoys.HasPlanarDrawingOn hG
  refine ⟨H, hGH, hH, ?_, hmax⟩
  intro u v
  induction hconn u v with
  | refl => exact Relation.ReflTransGen.refl
  | tail huv huvEdge ih =>
      exact Relation.ReflTransGen.tail ih (hGH huvEdge)