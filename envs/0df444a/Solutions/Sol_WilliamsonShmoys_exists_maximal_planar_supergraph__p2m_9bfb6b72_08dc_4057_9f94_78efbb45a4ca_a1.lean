-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_9bfb6b72_08dc_4057_9f94_78efbb45a4ca_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:23:21.789039+00:00
-- url     : https://prove2.me/submissions/cae89d43-02d4-4e05-ae4d-5324441dbb56

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_monotone_property_has_maximal_supergraph__p2m_1d8ac9c8_ae9e_4d86_8ce6_dc2f073f2eeb_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_subgraph__p2m_1d8ac9c8_ae9e_4d86_8ce6_dc2f073f2eeb_a1
set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ HasPlanarDrawingOn H ∧
      ∀ H' : SimpleGraph V, H ≤ H' → HasPlanarDrawingOn H' → H' = H := by
  exact WilliamsonShmoys.finite_monotone_property_has_maximal_supergraph__p2m_1d8ac9c8_ae9e_4d86_8ce6_dc2f073f2eeb_a1
    (Q := HasPlanarDrawingOn)
    (fun h hQ => WilliamsonShmoys.planar_drawing_subgraph__p2m_1d8ac9c8_ae9e_4d86_8ce6_dc2f073f2eeb_a1 h hQ)
    K hK