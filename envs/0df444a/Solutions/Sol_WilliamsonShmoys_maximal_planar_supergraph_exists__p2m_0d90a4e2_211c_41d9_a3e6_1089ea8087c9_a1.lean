-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_0d90a4e2_211c_41d9_a3e6_1089ea8087c9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:11:59.717486+00:00
-- url     : https://prove2.me/submissions/ce81abaf-a7f5-4fdc-9de1-307725f19c1f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_drawable_supergraph_max_arc_count__p2m_95b85285_7ea7_4e66_8526_e78475582691_a2
import Theorems.Thm_WilliamsonShmoys_strict_supergraph_increases_arc_count__p2m_95b85285_7ea7_4e66_8526_e78475582691_a2
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ H : SimpleGraph V, K ≤ H → HasPlanarDrawingOn H → H ≤ K := by
  obtain ⟨K, hGK, hK, hmax⟩ :=
    WilliamsonShmoys.finite_drawable_supergraph_max_arc_count__p2m_95b85285_7ea7_4e66_8526_e78475582691_a2
      G hG
  refine ⟨K, hGK, hK, ?_⟩
  intro H hKH hH
  by_contra hHK
  have hlt :=
    WilliamsonShmoys.strict_supergraph_increases_arc_count__p2m_95b85285_7ea7_4e66_8526_e78475582691_a2
      K H hKH hHK
  have hGH : G ≤ H := le_trans hGK hKH
  exact (not_lt_of_ge (hmax H hGH hH)) hlt