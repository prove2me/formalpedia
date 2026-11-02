-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_triangulation__p2m_3a2fa668_af0b_4223_89b0_dcabec19097b_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:56:22.477488+00:00
-- url     : https://prove2.me/submissions/95daa625-bbcb-49e6-8084-6792bdcb7eda
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_2313d792_5eb0_4345_85d6_32f091bb14d8_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_edge_count__p2m_2313d792_5eb0_4345_85d6_32f091bb14d8_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hGK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_2313d792_5eb0_4345_85d6_32f091bb14d8_a1
      G hG
  exact ⟨K, hGK, hK,
    WilliamsonShmoys.maximal_planar_drawingOn_edge_count__p2m_2313d792_5eb0_4345_85d6_32f091bb14d8_a1
      K hK hCard hmax⟩