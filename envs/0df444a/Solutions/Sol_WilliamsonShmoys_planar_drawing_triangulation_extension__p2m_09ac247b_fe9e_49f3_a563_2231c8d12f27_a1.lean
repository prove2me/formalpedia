-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_09ac247b_fe9e_49f3_a563_2231c8d12f27_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:45:10.034614+00:00
-- url     : https://prove2.me/submissions/55f35f81-f8a2-45e7-acd6-141fa7ce1ed6

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_extension__p2m_067ebb73_e756_4640_b5cf_ef3a010c6f28_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_067ebb73_e756_4640_b5cf_ef3a010c6f28_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hQ : HasPlanarDrawingOn Q) :
    ∃ R : SimpleGraph V,
      (∀ u v, Q.Adj u v → R.Adj u v) ∧
      HasPlanarDrawingOn R ∧
      (letI : DecidableRel Q.Adj := Classical.decRel Q.Adj
       letI : DecidableRel R.Adj := Classical.decRel R.Adj
       Q.edgeFinset.card ≤ R.edgeFinset.card) ∧
      (letI : DecidableRel R.Adj := Classical.decRel R.Adj
       R.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  classical
  obtain ⟨R, hQR, hR, hQleR, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_extension__p2m_067ebb73_e756_4640_b5cf_ef3a010c6f28_a1 Q hQ
  have hCount :=
    WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_067ebb73_e756_4640_b5cf_ef3a010c6f28_a1 R hcard hR hMax
  exact ⟨R, hQR, hR, hQleR, hCount⟩