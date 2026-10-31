-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_bound__p2m_6f3d39c4_bdd3_471f_b5e3_5e407be55c6e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:18:55.235833+00:00
-- url     : https://prove2.me/submissions/8b9ce0fb-dda0-45bb-a03b-b4d52937e472

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_6f3d39c4_bdd3_471f_b5e3_5e407be55c6e_a2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ (L : SimpleGraph V),
      (∀ ⦃u v : V⦄, K.Adj u v → L.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet.ncard ≤ K.edgeSet.ncard) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.maximal_planar_edge_bound__p2m_6f3d39c4_bdd3_471f_b5e3_5e407be55c6e_a2 K hK hconn hV hmax
