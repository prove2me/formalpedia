-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound__p2m_b89122c2_2828_407e_ad92_2701689cab61_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:34:44.28985+00:00
-- url     : https://prove2.me/submissions/f6cfe592-0536-4d47-8aa6-c435bedd952d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation__p2m_172ec1a1_67dd_48ed_9b1c_20de26385b63_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨K, hHK, hKplanar, hKcount⟩ :=
    WilliamsonShmoys.planar_supergraph_triangulation__p2m_172ec1a1_67dd_48ed_9b1c_20de26385b63_a1
      H hH hV
  omega