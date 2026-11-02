-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_a4257fd8_446b_43ed_ae2f_f84ba74a352a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:45:31.321748+00:00
-- url     : https://prove2.me/submissions/f00f699a-cce0-4532-9cfb-26127bab2ecd

import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_subgraph_closed__p2m_813de8ea_e58e_48bb_807f_43145eda7132_a1
import Theorems.Thm_WilliamsonShmoys_finite_maximal_supergraph_of_hereditary_property__p2m_813de8ea_e58e_48bb_807f_43145eda7132_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H := by
  obtain ⟨H, hGH, hH, hmax⟩ :=
    WilliamsonShmoys.finite_maximal_supergraph_of_hereditary_property__p2m_813de8ea_e58e_48bb_807f_43145eda7132_a1
      (P := HasPlanarDrawingOn) G hG
      (fun {A B} hAB hB =>
        WilliamsonShmoys.planarDrawingOn_subgraph_closed__p2m_813de8ea_e58e_48bb_807f_43145eda7132_a1 hAB hB)
  exact ⟨H, hGH, hH, hmax⟩