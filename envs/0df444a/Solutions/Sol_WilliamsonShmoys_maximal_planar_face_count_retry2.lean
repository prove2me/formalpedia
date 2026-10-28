-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_count_retry2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T06:18:23.385409+00:00
-- url     : https://prove2.me/submissions/1a55710c-263d-47ad-bb52-5ef869d1dac7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_from_curve_drawing

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : forall N : SimpleGraph V, M <= N ->
      WilliamsonShmoys.HasPlanarDrawingOn N -> N = M) :
    exists f : Nat,
      3 * (f : Int) = 2 * (M.edgeSet.ncard : Int) /\
      (Fintype.card V : Int) - (M.edgeSet.ncard : Int) + (f : Int) = 2 := by
  have hE : (M.edgeSet.ncard : Int) =
      3 * (Fintype.card V : Int) - 6 :=
    WilliamsonShmoys.maximal_planar_edge_count_from_curve_drawing M hV hM hMax
  refine Exists.intro (2 * Fintype.card V - 4) ?_
  constructor <;> omega