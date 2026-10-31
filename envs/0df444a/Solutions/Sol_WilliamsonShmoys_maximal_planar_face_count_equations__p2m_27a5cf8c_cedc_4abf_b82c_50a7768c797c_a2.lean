-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_count_equations__p2m_27a5cf8c_cedc_4abf_b82c_50a7768c797c_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:23:26.121667+00:00
-- url     : https://prove2.me/submissions/4a3062aa-7422-4ff5-8d2d-7b8540704ec3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_301f4675_a625_4f03_8421_053f86d64c99_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hG : HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V, G ≤ K → HasPlanarDrawingOn K → K = G) :
    ∃ f : ℕ,
      Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      3 * f = 2 * G.edgeSet.ncard := by
  have hE := WilliamsonShmoys.maximal_planar_edge_count__p2m_301f4675_a625_4f03_8421_053f86d64c99_a1
    G hV hG hmax
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega