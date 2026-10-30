-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_triangular_face_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T00:45:46.446016+00:00
-- url     : https://prove2.me/submissions/d5620b1a-3456-4d11-bc67-5acf4d221b7c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_from_maximality

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : forall M : SimpleGraph V, L <= M ->
      WilliamsonShmoys.HasPlanarDrawingOn M -> M = L)
    (hCard : 3 <= Fintype.card V)
    (f : Nat)
    (hEuler : Fintype.card V + f = L.edgeSet.ncard + 2) :
    3 * f = 2 * L.edgeSet.ncard := by
  have hEdge : L.edgeSet.ncard + 6 = 3 * Fintype.card V :=
    WilliamsonShmoys.maximal_planar_edge_count_from_maximality L hL hMax hCard
  omega
