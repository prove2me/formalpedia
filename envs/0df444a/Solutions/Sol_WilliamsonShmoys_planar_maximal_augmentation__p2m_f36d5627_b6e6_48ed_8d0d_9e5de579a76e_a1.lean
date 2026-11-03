-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_augmentation__p2m_f36d5627_b6e6_48ed_8d0d_9e5de579a76e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:52:15.778515+00:00
-- url     : https://prove2.me/submissions/a6cbb957-4397-4053-b1d7-a702eb32437b

import Theorems.Thm_WilliamsonShmoys_planar_maximal_augmentation__p2m_f36d5627_b6e6_48ed_8d0d_9e5de579a76e_a1__p2m_f36d5627_b6e6_48ed_8d0d_9e5de579a76e_a2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hn : 3 ≤ Fintype.card V) :
    ∃ (H : SimpleGraph V) (instH : DecidableRel H.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ u v, K.Adj u v → H.Adj u v) ∧
      (∀ (G' : SimpleGraph V), WilliamsonShmoys.HasPlanarDrawingOn G' →
        (∀ u v, H.Adj u v → G'.Adj u v) →
        (∀ u v, G'.Adj u v → H.Adj u v)) ∧
      (letI : DecidableRel H.Adj := instH; K.edgeFinset.card ≤ H.edgeFinset.card) :=
  WilliamsonShmoys.planar_maximal_augmentation__p2m_f36d5627_b6e6_48ed_8d0d_9e5de579a76e_a1__p2m_f36d5627_b6e6_48ed_8d0d_9e5de579a76e_a2 K hK hconn hn