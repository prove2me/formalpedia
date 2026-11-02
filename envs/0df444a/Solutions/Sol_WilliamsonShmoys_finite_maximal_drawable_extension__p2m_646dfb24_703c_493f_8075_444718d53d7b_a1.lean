-- Prove2me | solution 1 for WilliamsonShmoys_finite_maximal_drawable_extension__p2m_646dfb24_703c_493f_8075_444718d53d7b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:37:24.261199+00:00
-- url     : https://prove2.me/submissions/280a9aab-d4db-4286-a42b-757095e9e02f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_maximal_drawable_edge_count_extension__p2m_4ae5c893_7e52_474c_915d_3ed4ab7c0e94_a1
import Theorems.Thm_simpleGraph_extension_card_le_reverse__p2m_4ae5c893_7e52_474c_915d_3ed4ab7c0e94_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (P : SimpleGraph V → Prop) (hK : P K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ P H ∧
      (∀ G : SimpleGraph V, H ≤ G → P G → G ≤ H) ∧
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj
       letI : DecidableRel H.Adj := Classical.decRel H.Adj
       K.edgeFinset.card ≤ H.edgeFinset.card) := by
  classical
  obtain ⟨H, hKH, hPH, hMax⟩ :=
    finite_maximal_drawable_edge_count_extension__p2m_4ae5c893_7e52_474c_915d_3ed4ab7c0e94_a1
      K P hK
  refine ⟨H, hKH, hPH, ?_, ?_⟩
  · intro G hHG hPG
    have hKG : K ≤ G := le_trans hKH hHG
    have hcard := hMax G hKG hPG
    exact simpleGraph_extension_card_le_reverse__p2m_4ae5c893_7e52_474c_915d_3ed4ab7c0e94_a1
      H G hHG hcard
  · exact hMax K le_rfl hK
