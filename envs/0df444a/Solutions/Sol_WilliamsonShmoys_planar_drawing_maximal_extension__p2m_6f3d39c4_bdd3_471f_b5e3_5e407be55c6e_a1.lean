-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_6f3d39c4_bdd3_471f_b5e3_5e407be55c6e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:48:54.522878+00:00
-- url     : https://prove2.me/submissions/0fc0e7b4-b0bf-4c9d-a362-f5fc1cd0d3f2

import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_6f3d39c4_bdd3_471f_b5e3_5e407be55c6e_a2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected) :
    ∃ K : SimpleGraph V,
      (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.Connected ∧
      (∀ (L : SimpleGraph V),
        (∀ ⦃u v : V⦄, K.Adj u v → L.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        L.edgeSet.ncard ≤ K.edgeSet.ncard) ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard :=
  WilliamsonShmoys.planar_drawing_maximal_extension__p2m_6f3d39c4_bdd3_471f_b5e3_5e407be55c6e_a2 H hH hconn
