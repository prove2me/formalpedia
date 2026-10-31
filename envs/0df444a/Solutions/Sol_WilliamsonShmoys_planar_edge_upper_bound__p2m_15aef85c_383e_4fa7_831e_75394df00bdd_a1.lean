-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound__p2m_15aef85c_383e_4fa7_831e_75394df00bdd_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:22:52.855477+00:00
-- url     : https://prove2.me/submissions/feae8431-79f5-461b-b6e0-10b0619aabd3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_upper_bound__p2m_b041ba7e_9475_4324_b141_7c04552295c3_a1
import Theorems.Thm_WilliamsonShmoys_planar_spanning_connected_extension__p2m_b041ba7e_9475_4324_b141_7c04552295c3_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨K, hmono, hconn, hKplanar⟩ :=
    WilliamsonShmoys.planar_spanning_connected_extension__p2m_b041ba7e_9475_4324_b141_7c04552295c3_a1
      H hH
  have hK :=
    WilliamsonShmoys.connected_planar_edge_upper_bound__p2m_b041ba7e_9475_4324_b141_7c04552295c3_a1
      K hKplanar hconn hV
  omega