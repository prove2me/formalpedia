-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_augmentation__p2m_ac724374_f88c_4ddf_bad5_42fda9b092d4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:14:42.556564+00:00
-- url     : https://prove2.me/submissions/0453a143-b2b5-47a9-8eac-317b3165967e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_drawing_supergraph__p2m_7021208f_8613_4620_af29_8109890d733a_a1
import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_drawing__p2m_7021208f_8613_4620_af29_8109890d733a_a1

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V) (hS : WilliamsonShmoys.HasPlanarDrawingOn S)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel S.Adj := Classical.decRel S.Adj
    S.edgeFinset.card + 6 < 3 * Fintype.card V →
      ∃ T : SimpleGraph V,
        S ≤ T ∧ T ≠ S ∧ WilliamsonShmoys.HasPlanarDrawingOn T := by
  letI : DecidableRel S.Adj := Classical.decRel S.Adj
  intro hbound
  obtain ⟨T, hST, hT, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_drawing_supergraph__p2m_7021208f_8613_4620_af29_8109890d733a_a1
      S hS
  have hTcard :=
    WilliamsonShmoys.edge_count_of_maximal_planar_drawing__p2m_7021208f_8613_4620_af29_8109890d733a_a1
      T hT hcard hmax
  refine ⟨T, hST, ?_, hT⟩
  intro hEq
  subst T
  omega