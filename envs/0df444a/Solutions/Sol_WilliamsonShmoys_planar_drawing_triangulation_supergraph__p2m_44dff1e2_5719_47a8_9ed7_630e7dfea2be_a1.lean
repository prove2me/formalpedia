-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_supergraph__p2m_44dff1e2_5719_47a8_9ed7_630e7dfea2be_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T01:04:59.668481+00:00
-- url     : https://prove2.me/submissions/35befab5-ade9-4b2f-855c-228a5c73af9b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph__p2m_b4255e2c_f98e_48f5_8b5b_17ec5805d9ae_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_b4255e2c_f98e_48f5_8b5b_17ec5805d9ae_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 <= Fintype.card V) :
    ∃ T : SimpleGraph V, M ≤ T ∧
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      T.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨T, hMT, hDrawT, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_b4255e2c_f98e_48f5_8b5b_17ec5805d9ae_a1
      M hDraw
  exact ⟨T, hMT, hDrawT,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_b4255e2c_f98e_48f5_8b5b_17ec5805d9ae_a1
      T hDrawT hCard hmax⟩