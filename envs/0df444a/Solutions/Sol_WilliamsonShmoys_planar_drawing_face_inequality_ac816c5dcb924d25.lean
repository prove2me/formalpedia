-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_inequality_ac816c5dcb924d25
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:26:50.68411+00:00
-- url     : https://prove2.me/submissions/b5f03801-0b54-4d91-9c86-8eb3e802b974

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_bounds

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    exists f : Nat,
      Fintype.card V + f = H.edgeSet.ncard + 2 /\
      3 * f <= 2 * H.edgeSet.ncard := by
  have hBounds := WilliamsonShmoys.planar_edge_count_bounds H hV hconn hH
  have hconnEdges := hBounds.1
  have hplanarEdges := hBounds.2
  refine Exists.intro (H.edgeSet.ncard + 2 - Fintype.card V) ?_
  apply And.intro
  all_goals omega
