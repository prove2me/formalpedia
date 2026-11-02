-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_285fd92f_ac7f_4984_a234_6720989533e3_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:15:04.415266+00:00
-- url     : https://prove2.me/submissions/21dc897c-573b-4c63-8fd5-883aa2adc784

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_maximal_extension__p2m_89a3e2c0_b2b3_4ebc_a282_9a392a489cfc_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_89a3e2c0_b2b3_4ebc_a282_9a392a489cfc_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ HasPlanarDrawingOn K ∧
        (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
         3 * Fintype.card V = K.edgeFinset.card + 6) := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_maximal_extension__p2m_89a3e2c0_b2b3_4ebc_a282_9a392a489cfc_a1
      H hV hH
  exact ⟨K, hHK, hK,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_89a3e2c0_b2b3_4ebc_a282_9a392a489cfc_a1
      K hV hK hmax⟩