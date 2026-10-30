-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_b0a02e34_0eef_479c_ba08_d5e8c6d2e779_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T08:00:29.820984+00:00
-- url     : https://prove2.me/submissions/3faf5841-6055-4d0c-aa2d-cf79b5f7f635
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_58d8e6f3_93b9_4006_85ea_c7e3275fd746_a5
import Theorems.Thm_WilliamsonShmoys_maximal_planar_euler__p2m_58d8e6f3_93b9_4006_85ea_c7e3275fd746_a5
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_incidence__p2m_58d8e6f3_93b9_4006_85ea_c7e3275fd746_a5

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : HasPlanarDrawingOn H) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨M, hHM, hMdraw, hMax, hEdges⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph__p2m_58d8e6f3_93b9_4006_85ea_c7e3275fd746_a5
      H hH
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.maximal_planar_euler__p2m_58d8e6f3_93b9_4006_85ea_c7e3275fd746_a5
      M hMdraw hMax hV
  have hIncidence :=
    WilliamsonShmoys.maximal_planar_face_incidence__p2m_58d8e6f3_93b9_4006_85ea_c7e3275fd746_a5
      M hMdraw hMax hV f hEuler
  omega