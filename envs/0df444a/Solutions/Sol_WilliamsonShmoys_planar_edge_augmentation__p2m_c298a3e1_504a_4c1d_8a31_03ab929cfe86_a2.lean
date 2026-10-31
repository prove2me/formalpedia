-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_augmentation__p2m_c298a3e1_504a_4c1d_8a31_03ab929cfe86_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:12:52.745927+00:00
-- url     : https://prove2.me/submissions/ecfa88d6-a1e5-485e-a6dc-747a00e6f547

import Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_below_max_20261026

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hCard : 3 ≤ Fintype.card V)
    (hSparse : P.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ Q : SimpleGraph V,
      P ≤ Q ∧ Q ≠ P ∧ WilliamsonShmoys.HasPlanarDrawingOn Q :=
  WilliamsonShmoys.planar_edge_augmentation_below_max_20261026 P hDraw hCard hSparse
