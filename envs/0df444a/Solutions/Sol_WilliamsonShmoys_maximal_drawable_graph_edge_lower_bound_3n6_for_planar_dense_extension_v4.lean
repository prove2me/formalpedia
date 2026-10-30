-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound_3n6_for_planar_dense_extension_v4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:48:05.686107+00:00
-- url     : https://prove2.me/submissions/029e61d0-80e9-4f4a-8ccf-81abecb0de09

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulating_supergraph_for_maximal_drawable_graph_edge_lower_bound_3n6_v4

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hMax : forall Q : SimpleGraph V, P <= Q -> WilliamsonShmoys.HasPlanarDrawingOn Q -> Q <= P) :
    3 * Fintype.card V - 6 <= P.edgeSet.ncard := by
  let htri :=
    WilliamsonShmoys.planar_graph_has_triangulating_supergraph_for_maximal_drawable_graph_edge_lower_bound_3n6_v4
      P hV hP
  let Q := Classical.choose htri
  let hspec := Classical.choose_spec htri
  have hPQ : P <= Q := hspec.1
  have hQ : WilliamsonShmoys.HasPlanarDrawingOn Q := hspec.2.1
  have hcard : Q.edgeSet.ncard = 3 * Fintype.card V - 6 := hspec.2.2
  have hQP : Q <= P := hMax Q hPQ hQ
  have hEq : Q = P := le_antisymm hQP hPQ
  have hbound : 3 * Fintype.card V - 6 <= Q.edgeSet.ncard :=
    Nat.le_of_eq hcard.symm
  simpa [hEq] using hbound
