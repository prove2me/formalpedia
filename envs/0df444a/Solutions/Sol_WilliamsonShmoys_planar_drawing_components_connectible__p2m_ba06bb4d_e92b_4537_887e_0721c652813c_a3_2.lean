-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_components_connectible__p2m_ba06bb4d_e92b_4537_887e_0721c652813c_a3
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:15:40.363477+00:00
-- url     : https://prove2.me/submissions/a8abe435-5696-4ac5-8ae0-3824c956305a

import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation_with_three_vertices
import Mathlib

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ K.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      H.edgeSet.ncard <= K.edgeSet.ncard :=
  WilliamsonShmoys.planar_drawing_connected_augmentation_with_three_vertices H hH hcard
