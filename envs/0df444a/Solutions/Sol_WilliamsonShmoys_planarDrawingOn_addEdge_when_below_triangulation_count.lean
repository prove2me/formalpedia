-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_addEdge_when_below_triangulation_count
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:39:34.807881+00:00
-- url     : https://prove2.me/submissions/422801bb-3ccb-48b4-84bb-84acc64a6dbf

import Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_below_bound__p2m_03ed2ab0_efc9_4bea_b7ff_50f9e41807dc_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hS : WilliamsonShmoys.HasPlanarDrawingOn S)
    (hCard : 3 ≤ Fintype.card V)
    (hBelow : S.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ T : SimpleGraph V, S < T ∧ WilliamsonShmoys.HasPlanarDrawingOn T :=
  WilliamsonShmoys.planar_edge_augmentation_below_bound__p2m_03ed2ab0_efc9_4bea_b7ff_50f9e41807dc_a1 S hS hCard hBelow
