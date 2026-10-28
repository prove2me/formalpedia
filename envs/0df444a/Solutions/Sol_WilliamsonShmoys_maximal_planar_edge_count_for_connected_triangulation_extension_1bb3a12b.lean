-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_for_connected_triangulation_extension_1bb3a12b
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T18:36:23.161352+00:00
-- url     : https://prove2.me/submissions/680c2588-934e-44a1-8c72-87aebd005e9d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper_bound_d6e88113
import Theorems.Thm_WilliamsonShmoys_maximal_planar_triangulation_extension_d6e88113

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn H) (hconn : H.Connected)
    (hmax : ∀ K : SimpleGraph V, HasPlanarDrawingOn K →
      (∀ u v, H.Adj u v → K.Adj u v) →
      K.edgeSet.ncard ≤ H.edgeSet.ncard)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper := WilliamsonShmoys.maximal_planar_edge_count_upper_bound_d6e88113
    H hdraw hV
  obtain ⟨K, hKdraw, hHK, hKcount⟩ :=
    WilliamsonShmoys.maximal_planar_triangulation_extension_d6e88113
      H hdraw hconn hV
  have hmaxK := hmax K hKdraw hHK
  omega