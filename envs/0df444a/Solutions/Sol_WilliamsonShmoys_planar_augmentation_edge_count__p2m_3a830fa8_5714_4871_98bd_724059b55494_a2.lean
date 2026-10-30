-- Prove2me | solution 1 for WilliamsonShmoys.planar_augmentation_edge_count__p2m_3a830fa8_5714_4871_98bd_724059b55494_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T23:07:19.90845+00:00
-- url     : https://prove2.me/submissions/4f0336a8-85b8-49ca-9615-fa466a899e43

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_augmentation_maximal_supergraph__p2m_c063ecbf_b4be_428e_95f9_2de36a0b9a32_a1
import Theorems.Thm_WilliamsonShmoys_planar_maximal_graph_edge_count__p2m_c063ecbf_b4be_428e_95f9_2de36a0b9a32_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 <= Fintype.card V) :
    exists K : SimpleGraph V,
      H <= K /\ WilliamsonShmoys.HasPlanarDrawingOn K /\
        K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_augmentation_maximal_supergraph__p2m_c063ecbf_b4be_428e_95f9_2de36a0b9a32_a1
      H hH
  exact ⟨K, hHK, hK,
    WilliamsonShmoys.planar_maximal_graph_edge_count__p2m_c063ecbf_b4be_428e_95f9_2de36a0b9a32_a1
      K hK hCard hmax⟩