-- Prove2me | solution 1 for WilliamsonShmoys.planar_extension_to_inclusion_maximal__p2m_bc67589b_3983_4963_b1d8_6aabd3b931c4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:39:14.739205+00:00
-- url     : https://prove2.me/submissions/b26c0e2c-384a-449a-a229-b29010b4f4aa

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_finite_hereditary_property_has_maximal_extension__p2m_918f6ef7_b742_4a7a_b6c7_f41fd05476c6_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_subgraph__p2m_918f6ef7_b742_4a7a_b6c7_f41fd05476c6_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.finite_hereditary_property_has_maximal_extension__p2m_918f6ef7_b742_4a7a_b6c7_f41fd05476c6_a1
      (P := HasPlanarDrawingOn) (K := K) hK
      (fun {G H} hGH hH =>
        WilliamsonShmoys.planar_drawing_subgraph__p2m_918f6ef7_b742_4a7a_b6c7_f41fd05476c6_a1
          hGH hH)
  exact ⟨L, hKL, hL, hmax⟩