-- Prove2me | solution 2 for WilliamsonShmoys.planar_triangulation_augmentation__p2m_c356afa4_3905_47c7_8a37_a6d010ebe354_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:40:41.924492+00:00
-- url     : https://prove2.me/submissions/17379a7a-f255-4c0e-b59a-2e3f003e4616

import Theorems.Thm_WilliamsonShmoys_planar_augmentation_to_maximal_edge_count

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ T : SimpleGraph V, H ≤ T ∧
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      T.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_augmentation_to_maximal_edge_count H hV hH
