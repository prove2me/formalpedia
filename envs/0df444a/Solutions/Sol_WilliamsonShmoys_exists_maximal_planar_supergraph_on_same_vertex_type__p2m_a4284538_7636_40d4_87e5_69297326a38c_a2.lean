-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph_on_same_vertex_type__p2m_a4284538_7636_40d4_87e5_69297326a38c_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:48:02.184307+00:00
-- url     : https://prove2.me/submissions/edc1ca1e-b1c4-4cbf-ba95-a54cdc8c1a70

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_maximal_extension_of_finite__p2m_5269810a_aaa3_482e_ac1c_32cbc68ffb91_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_on_subgraph__p2m_5269810a_aaa3_482e_ac1c_32cbc68ffb91_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdrawing : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K := by
  exact WilliamsonShmoys.exists_maximal_extension_of_finite__p2m_5269810a_aaa3_482e_ac1c_32cbc68ffb91_a1
    (P := HasPlanarDrawingOn) (hhered := by
      intro G K hGK hK
      exact WilliamsonShmoys.planar_drawing_on_subgraph__p2m_5269810a_aaa3_482e_ac1c_32cbc68ffb91_a1 hGK hK)
    H hdrawing