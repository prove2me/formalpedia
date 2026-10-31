-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulated_supergraph_edge_bound__p2m_0b3a5bc9_5212_4922_863b_b35f1f108c76_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:31:21.973904+00:00
-- url     : https://prove2.me/submissions/a1810069-9ce2-411e-856a-bf90317c12f6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_maximal_supergraph__p2m_12adc1a9_2da3_4bce_a578_d16f94d48e85_a1
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_edge_bound__p2m_12adc1a9_2da3_4bce_a578_d16f94d48e85_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  obtain ⟨K, hHK, hK, hMax⟩ :=
    WilliamsonShmoys.planar_edge_maximal_supergraph__p2m_12adc1a9_2da3_4bce_a578_d16f94d48e85_a1
      H hH
  exact ⟨K, hHK, hK,
    WilliamsonShmoys.edge_maximal_planar_edge_bound__p2m_12adc1a9_2da3_4bce_a578_d16f94d48e85_a1
      K hK hCard hMax⟩