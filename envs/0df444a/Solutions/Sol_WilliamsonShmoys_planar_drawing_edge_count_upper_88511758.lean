-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_upper_88511758
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T03:01:17.8853+00:00
-- url     : https://prove2.me/submissions/32e4bada-a7e3-497f-aacc-f7fc92091ef0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_6357fee1_f927_4c5b_a160_dca513168a22
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨K, hHK, hKplanar, hKeq, hcard⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_6357fee1_f927_4c5b_a160_dca513168a22
      H hV hconn hH
  omega