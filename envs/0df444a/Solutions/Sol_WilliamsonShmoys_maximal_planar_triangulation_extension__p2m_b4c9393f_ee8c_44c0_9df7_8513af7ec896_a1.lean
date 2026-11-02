-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_triangulation_extension__p2m_b4c9393f_ee8c_44c0_9df7_8513af7ec896_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:04:02.793715+00:00
-- url     : https://prove2.me/submissions/0c8f3b14-1301-4be8-8dac-d22cbf2e269c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_extension__p2m_18964b7c_c181_43c8_b19b_00116e3fbbcb_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_18964b7c_c181_43c8_b19b_00116e3fbbcb_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ (K : SimpleGraph V) (_ : DecidableRel K.Adj),
      H.edgeFinset ⊆ K.edgeFinset ∧
      HasPlanarDrawingOn K ∧
      K.edgeFinset.card = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hDecK, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_extension__p2m_18964b7c_c181_43c8_b19b_00116e3fbbcb_a2
      H hH
  letI : DecidableRel K.Adj := hDecK
  refine ⟨K, hDecK, hHK, hK, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_18964b7c_c181_43c8_b19b_00116e3fbbcb_a2
    K hK hV hmax