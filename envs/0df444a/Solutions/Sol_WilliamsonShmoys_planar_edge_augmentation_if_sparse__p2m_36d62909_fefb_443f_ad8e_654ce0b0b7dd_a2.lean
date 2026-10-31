-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_augmentation_if_sparse__p2m_36d62909_fefb_443f_ad8e_654ce0b0b7dd_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:02:15.841226+00:00
-- url     : https://prove2.me/submissions/6819886d-a2d2-4508-8859-825dc3c83a73

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph__p2m_a5cf4edc_e88b_40ef_a197_b0d2fda5eb44_a1
import Theorems.Thm_WilliamsonShmoys_edge_count_of_edge_maximal_planar__p2m_a5cf4edc_e88b_40ef_a197_b0d2fda5eb44_a1
import Theorems.Thm_WilliamsonShmoys_edge_count_mono_of_graph_le__p2m_a5cf4edc_e88b_40ef_a197_b0d2fda5eb44_a1
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V)
    (hSparse : K.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ L ≠ K ∧ HasPlanarDrawingOn L := by
  obtain ⟨L, hKL, hDrawL, hMax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_a5cf4edc_e88b_40ef_a197_b0d2fda5eb44_a1 K hK
  have hCount :=
    WilliamsonShmoys.edge_count_of_edge_maximal_planar__p2m_a5cf4edc_e88b_40ef_a197_b0d2fda5eb44_a1 L hV hDrawL hMax
  have hMono :=
    WilliamsonShmoys.edge_count_mono_of_graph_le__p2m_a5cf4edc_e88b_40ef_a197_b0d2fda5eb44_a1 hKL
  have hStrict : K.edgeSet.ncard + 6 < L.edgeSet.ncard + 6 := by omega
  have hNe : L ≠ K := by
    intro hEq
    subst L
    omega
  exact ⟨L, hKL, hNe, hDrawL⟩