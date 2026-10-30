-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_9e09229e_d4ec_4237_9818_555f2ee4ea2a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:24:15.05785+00:00
-- url     : https://prove2.me/submissions/541c0d51-87e1-494a-8ad6-d8b0c5c67558

import Theorems.Thm_finite_simpleGraph_maximal_supergraph__p2m_8526028d_6503_4baf_b95b_7d2634d3c3de_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) : ∃ K : SimpleGraph V, L ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ (∀ H : SimpleGraph V, K ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ K) := by
  exact finite_simpleGraph_maximal_supergraph__p2m_8526028d_6503_4baf_b95b_7d2634d3c3de_a1
    WilliamsonShmoys.HasPlanarDrawingOn L hL