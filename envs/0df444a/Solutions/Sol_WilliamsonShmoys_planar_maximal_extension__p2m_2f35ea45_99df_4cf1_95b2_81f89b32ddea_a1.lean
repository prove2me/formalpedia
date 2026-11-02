-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_extension__p2m_2f35ea45_99df_4cf1_95b2_81f89b32ddea_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:30:27.795012+00:00
-- url     : https://prove2.me/submissions/5cbaea9d-0240-4200-bcbc-fbc5986ed6ad

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_graph_property_maximal_extension__p2m_f1c70f2e_734a_4ab3_9ef1_4b1e0b3c2cfc_a1
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hn : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K := by
  exact WilliamsonShmoys.finite_graph_property_maximal_extension__p2m_f1c70f2e_734a_4ab3_9ef1_4b1e0b3c2cfc_a1
    (P := HasPlanarDrawingOn) H hH