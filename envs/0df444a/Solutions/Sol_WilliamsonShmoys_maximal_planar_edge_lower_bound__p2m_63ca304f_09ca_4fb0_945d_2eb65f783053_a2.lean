-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_63ca304f_09ca_4fb0_945d_2eb65f783053_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T02:05:45.70998+00:00
-- url     : https://prove2.me/submissions/94f9ab4c-dd58-4af4-9052-087639b79177

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawing_face_certificate__p2m_3003f6fd_5536_41b8_8ede_329302ccc292_a3

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet ⊆ K.edgeSet)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.maximal_drawing_face_certificate__p2m_3003f6fd_5536_41b8_8ede_329302ccc292_a3
      K hDraw hmax hV
  omega