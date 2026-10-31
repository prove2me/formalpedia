-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_6a98dd8c_93db_41f3_b936_6f734f02a42e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:59:50.483313+00:00
-- url     : https://prove2.me/submissions/837acc7b-6800-40d3-8c0c-c84dcfdcf4c8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_dc9018d8_e47b_47c1_8eef_84ccb4273562_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition__p2m_dc9018d8_e47b_47c1_8eef_84ccb4273562_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ T : SimpleGraph V, G ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧
      T.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨T, hGT, hT, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_dc9018d8_e47b_47c1_8eef_84ccb4273562_a1
      G hG
  obtain ⟨f, hEuler, hIncidence⟩ :=
    WilliamsonShmoys.maximal_planar_face_decomposition__p2m_dc9018d8_e47b_47c1_8eef_84ccb4273562_a1
      T hT hmax hV
  refine ⟨T, hGT, hT, ?_⟩
  omega