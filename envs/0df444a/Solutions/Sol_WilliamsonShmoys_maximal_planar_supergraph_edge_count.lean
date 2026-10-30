-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T10:24:19.568986+00:00
-- url     : https://prove2.me/submissions/5d60d2eb-02fb-4767-a36b-ec97c99c988c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_edge_count_bound_euler
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_euler

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V, G ≤ K → HasPlanarDrawingOn K → K = G)
    (hcard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper : G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
    WilliamsonShmoys.planar_simple_edge_count_bound_euler G hG hcard
  have hlower : 3 * Fintype.card V ≤ G.edgeSet.ncard + 6 :=
    WilliamsonShmoys.maximal_planar_edge_count_lower_bound_euler G hG hmax hcard
  omega