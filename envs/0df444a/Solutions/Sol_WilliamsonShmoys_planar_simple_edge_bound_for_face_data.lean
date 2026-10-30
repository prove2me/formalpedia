-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_edge_bound_for_face_data
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T13:53:48.216276+00:00
-- url     : https://prove2.me/submissions/42b17717-02b1-4364-a3c5-bf4a3de9f1ed

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_supergraph_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hConn : forall u v, Relation.ReflTransGen J.Adj u v)
    (hV : 3 <= Fintype.card V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    J.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨K, hsub, hK⟩ :=
    WilliamsonShmoys.planar_edge_supergraph_bound J hConn hV hJ
  exact le_trans (Nat.add_le_add_right (Set.ncard_mono hsub) 6) hK