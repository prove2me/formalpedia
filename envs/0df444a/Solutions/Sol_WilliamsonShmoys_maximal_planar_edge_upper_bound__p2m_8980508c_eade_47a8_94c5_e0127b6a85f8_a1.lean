-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_upper_bound__p2m_8980508c_eade_47a8_94c5_e0127b6a85f8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:21:03.552642+00:00
-- url     : https://prove2.me/submissions/9412a578-cb96-4c2c-b93b-2970e47f6011

import Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_b89122c2_2828_407e_ad92_2701689cab61_a1
import Mathlib

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ H' : SimpleGraph V,
      Set.Subset H.edgeSet H'.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn H' →
      H'.edgeSet = H.edgeSet) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_bound__p2m_b89122c2_2828_407e_ad92_2701689cab61_a1 H hdraw hV
