-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_5f0f808e_c07c_4234_8a22_35ebffc68b17_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:08:44.372352+00:00
-- url     : https://prove2.me/submissions/184ae895-bfeb-4194-aa24-b06ac3cd5c2c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_extension__p2m_19232441_686a_4272_ba92_bbecb802c741_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ L : SimpleGraph V, H ≤ L → L ≠ H →
        ¬ WilliamsonShmoys.HasPlanarDrawingOn L := by
  exact WilliamsonShmoys.finite_maximal_extension__p2m_19232441_686a_4272_ba92_bbecb802c741_a1
    WilliamsonShmoys.HasPlanarDrawingOn K hK