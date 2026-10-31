-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_extension__p2m_6301d38c_0224_4362_a676_de729a46b58e_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:10:30.032952+00:00
-- url     : https://prove2.me/submissions/8f422233-6dc1-4840-9fd9-b6e546f866e7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_predicate_has_maximal_supergraph__p2m_8fae69ca_ae24_46cb_a1af_2dc3b1fd2851_a2
import Theorems.Thm_WilliamsonShmoys_planar_drawing_subgraph__p2m_8fae69ca_ae24_46cb_a1af_2dc3b1fd2851_a2

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V)
    (hN : HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ N.edgeSet.ncard ≤ K.edgeSet.ncard ∧ HasPlanarDrawingOn K ∧
        ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K := by
  exact WilliamsonShmoys.finite_predicate_has_maximal_supergraph__p2m_8fae69ca_ae24_46cb_a1af_2dc3b1fd2851_a2
    HasPlanarDrawingOn N hN
    (by
      intro A B hAB hB
      exact WilliamsonShmoys.planar_drawing_subgraph__p2m_8fae69ca_ae24_46cb_a1af_2dc3b1fd2851_a2 hAB hB)