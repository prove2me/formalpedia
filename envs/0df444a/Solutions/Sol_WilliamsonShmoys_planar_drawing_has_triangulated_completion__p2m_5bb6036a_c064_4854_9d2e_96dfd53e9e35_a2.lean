-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_triangulated_completion__p2m_5bb6036a_c064_4854_9d2e_96dfd53e9e35_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:40:39.892686+00:00
-- url     : https://prove2.me/submissions/44f5f136-8678-4381-8287-d1ae703aeec9

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_drawable_extension__p2m_64f9a932_9abc_4892_8345_6d855cf8c7f4_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_euler_edge_count__p2m_64f9a932_9abc_4892_8345_6d855cf8c7f4_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hN : HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V, N ≤ K ∧ HasPlanarDrawingOn K ∧
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
       3 * Fintype.card V - 6 = K.edgeFinset.card) := by
  obtain ⟨K, hNK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_drawable_extension__p2m_64f9a932_9abc_4892_8345_6d855cf8c7f4_a1
      N hN
  refine ⟨K, hNK, hK, ?_⟩
  exact WilliamsonShmoys.maximal_planar_drawing_has_euler_edge_count__p2m_64f9a932_9abc_4892_8345_6d855cf8c7f4_a1
    K hV hK hmax