-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_maximal_planar_extension__p2m_ad02c9e2_6f74_49a1_ae0d_05fd18f8b6b9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:54:54.009196+00:00
-- url     : https://prove2.me/submissions/91ed2e1d-d4ab-4bfa-be0a-32b05962d835

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_maximal_extension__p2m_03bfe837_ddc7_49ff_ba57_41dcefd0c29f_a1
import Theorems.Thm_hasPlanarDrawingOn_mono__p2m_03bfe837_ddc7_49ff_ba57_41dcefd0c29f_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ H : SimpleGraph V,
      N ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        ∀ K : SimpleGraph V, H ≤ K →
          WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by
  classical
  letI : Fintype (SimpleGraph V) := Fintype.ofFinite _
  exact finite_maximal_extension__p2m_03bfe837_ddc7_49ff_ba57_41dcefd0c29f_a1
    WilliamsonShmoys.HasPlanarDrawingOn
    (by
      intro H G hHG hG
      exact hasPlanarDrawingOn_mono__p2m_03bfe837_ddc7_49ff_ba57_41dcefd0c29f_a1 hHG hG)
    N hN