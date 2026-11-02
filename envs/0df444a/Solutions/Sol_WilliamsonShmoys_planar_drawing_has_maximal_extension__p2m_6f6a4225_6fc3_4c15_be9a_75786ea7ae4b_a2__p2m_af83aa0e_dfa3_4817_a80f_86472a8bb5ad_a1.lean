-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_extension__p2m_6f6a4225_6fc3_4c15_be9a_75786ea7ae4b_a2__p2m_af83aa0e_dfa3_4817_a80f_86472a8bb5ad_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:20:41.634944+00:00
-- url     : https://prove2.me/submissions/3f41c9eb-975a-4cc5-9afc-b42717b74835

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_finite_graph_predicate_has_edge_max__p2m_5f4c0396_f2c5_4ee4_89c1_d7bcb4050c5c_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L) :
    letI : (G : SimpleGraph V) -> DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    ∃ H : SimpleGraph V, L ≤ H ∧ HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, L ≤ K → HasPlanarDrawingOn K →
        K.edgeFinset.card ≤ H.edgeFinset.card) := by
  classical
  letI : (G : SimpleGraph V) -> DecidableRel G.Adj := fun G => Classical.decRel G.Adj
  obtain ⟨H, hH, hmax⟩ :=
    WilliamsonShmoys.finite_graph_predicate_has_edge_max__p2m_5f4c0396_f2c5_4ee4_89c1_d7bcb4050c5c_a1
      (V := V) (P := fun G => L ≤ G ∧ HasPlanarDrawingOn G)
      ⟨L, le_rfl, hL⟩
  refine ⟨H, hH.1, hH.2, ?_⟩
  intro K hLK hK
  exact hmax K ⟨hLK, hK⟩