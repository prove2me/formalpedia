-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_ed86bc60_f31a_467f_bd4d_ab190f9b728c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:36:08.490676+00:00
-- url     : https://prove2.me/submissions/b53cf322-25f1-446f-93f7-af6efc7ae507

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_max_card_planar_supergraph__p2m_3e744d16_fd12_4405_889b_d7d7bae50b90_a1
import Theorems.Thm_WilliamsonShmoys_eq_of_subgraph_and_edge_card_le__p2m_3e744d16_fd12_4405_889b_d7d7bae50b90_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ M : SimpleGraph V,
          L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by
  obtain ⟨L, hKL, hDrawL, hmax⟩ :=
    WilliamsonShmoys.exists_max_card_planar_supergraph__p2m_3e744d16_fd12_4405_889b_d7d7bae50b90_a1
      K hDraw
  refine ⟨L, hKL, hDrawL, ?_⟩
  intro M hLM hDrawM
  have hcard := hmax M (le_trans hKL hLM) hDrawM hLM
  exact
    (WilliamsonShmoys.eq_of_subgraph_and_edge_card_le__p2m_3e744d16_fd12_4405_889b_d7d7bae50b90_a1
      L M hLM hcard).symm