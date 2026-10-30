-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_decomposition__p2m_2f707832_942f_4ae9_9944_7f0d941152ce_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T12:42:02.473668+00:00
-- url     : https://prove2.me/submissions/7a9f4a3d-551f-4b2d-9b61-1a7820db630b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_euler__p2m_cc582279_bd81_4049_86d4_e111019c4e0a_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_incidence__p2m_cc582279_bd81_4049_86d4_e111019c4e0a_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K.edgeSet ⊂ L.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f = 2 * K.edgeSet.ncard := by
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.maximal_planar_euler__p2m_cc582279_bd81_4049_86d4_e111019c4e0a_a1
      K hK hmax hV
  exact ⟨f, hEuler,
    WilliamsonShmoys.maximal_planar_face_incidence__p2m_cc582279_bd81_4049_86d4_e111019c4e0a_a1
      K hK hmax hV f hEuler⟩