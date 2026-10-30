-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_completion__p2m_f10915d7_3b63_441c_afee_bba7154a1b1e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:21:28.905457+00:00
-- url     : https://prove2.me/submissions/5060577b-409d-48c8-b6bd-ceac7884e68d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_supergraph_property_maximal__p2m_c7aec4eb_c4f1_4807_be6d_30dcecf57431_a1
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      L.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ M : SimpleGraph V, H.edgeSet ⊆ M.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn M → H = M := by
  obtain ⟨H, hLH, hH, hmax⟩ :=
    WilliamsonShmoys.finite_supergraph_property_maximal__p2m_c7aec4eb_c4f1_4807_be6d_30dcecf57431_a1
      L WilliamsonShmoys.HasPlanarDrawingOn hDraw
  exact ⟨H, hLH, hH, fun M hHM hM => hmax M hHM hM⟩