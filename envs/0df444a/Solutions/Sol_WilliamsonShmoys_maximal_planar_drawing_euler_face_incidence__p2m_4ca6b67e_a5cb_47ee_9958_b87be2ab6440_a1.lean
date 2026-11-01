-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_euler_face_incidence__p2m_4ca6b67e_a5cb_47ee_9958_b87be2ab6440_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:47:03.594191+00:00
-- url     : https://prove2.me/submissions/e919b5e8-7cff-4132-9f4c-7445f1eb1c36
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_5de819de_a434_4eee_9d51_0646a941be0a_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn K →
      H.edgeFinset ⊆ K.edgeFinset →
      K.edgeFinset ⊆ H.edgeFinset) :
    ∃ f : ℕ,
      Fintype.card V + f = H.edgeFinset.card + 2 ∧
      3 * f = 2 * H.edgeFinset.card := by
  have hEdge :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_5de819de_a434_4eee_9d51_0646a941be0a_a1
      H dH hH hcard hmax
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega