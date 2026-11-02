-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_maximal_extension__p2m_5b23b791_8f68_4090_90fa_7eb62c80871a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:12:05.225355+00:00
-- url     : https://prove2.me/submissions/d4f3efd3-3780-4cb6-9ea2-4d40e263a37a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_drawable_supergraph_maximal__p2m_e472cbd3_427a_4623_8f32_b9aff130ed8d_a2
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (Q : SimpleGraph V)
    (hQ : HasPlanarDrawingOn Q) (hcard : 3 ≤ Fintype.card V) :
    ∃ R : SimpleGraph V, Q ≤ R ∧ HasPlanarDrawingOn R ∧
      ∀ S : SimpleGraph V, R ≤ S → HasPlanarDrawingOn S → S = R := by
  exact WilliamsonShmoys.finite_drawable_supergraph_maximal__p2m_e472cbd3_427a_4623_8f32_b9aff130ed8d_a2 Q hQ