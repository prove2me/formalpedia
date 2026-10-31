-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_augmentation__p2m_bf9be5f4_efbc_4928_a7c5_3fcb68a1a21a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:25:33.363506+00:00
-- url     : https://prove2.me/submissions/a728c765-14f0-497b-962d-2ce4b8be0962

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_1fc721c4_d4d8_4a3d_8e5b_8d3e1462bbc6_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_bound__p2m_1fc721c4_d4d8_4a3d_8e5b_8d3e1462bbc6_a1

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V) (hS : HasPlanarDrawingOn S)
    (hCard : 3 ≤ Fintype.card V)
    (hSmall : S.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ T : SimpleGraph V, S ≤ T ∧ T ≠ S ∧ HasPlanarDrawingOn T := by
  obtain ⟨T, hST, hT, hMax⟩ := WilliamsonShmoys.planar_drawing_maximal_extension__p2m_1fc721c4_d4d8_4a3d_8e5b_8d3e1462bbc6_a1 S hS
  have hbound := WilliamsonShmoys.maximal_planar_drawing_edge_bound__p2m_1fc721c4_d4d8_4a3d_8e5b_8d3e1462bbc6_a1 T hT hCard hMax
  have hne : T ≠ S := by
    intro hEq
    subst T
    omega
  exact ⟨T, hST, hne, hT⟩