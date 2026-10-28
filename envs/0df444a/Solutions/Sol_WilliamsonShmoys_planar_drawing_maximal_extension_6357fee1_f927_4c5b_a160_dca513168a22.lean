-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension_6357fee1_f927_4c5b_a160_dca513168a22
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T03:19:37.870125+00:00
-- url     : https://prove2.me/submissions/61ac4317-700f-4e00-b185-c3527b744344
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extension_to_maximal_6357fee1_f927_4c5b_a160_dca513168a22
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_6357fee1_f927_4c5b_a160_dca513168a22

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    Exists fun K : SimpleGraph V =>
      And (H <= K) (And (WilliamsonShmoys.HasPlanarDrawingOn K)
        (And (K.edgeSet.ncard + 6 = 3 * Fintype.card V)
          (H.edgeSet.ncard <= K.edgeSet.ncard))) := by
  have hExt :=
    WilliamsonShmoys.planar_drawing_extension_to_maximal_6357fee1_f927_4c5b_a160_dca513168a22 H hH
  exact Exists.elim hExt (fun K hK =>
    let hCount :=
      WilliamsonShmoys.maximal_planar_drawing_edge_count_6357fee1_f927_4c5b_a160_dca513168a22
        K hV hK.2.1 hK.2.2.2
    Exists.intro K (And.intro hK.1 (And.intro hK.2.1
      (And.intro hCount hK.2.2.1))))