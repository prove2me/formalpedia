-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_augmentation__p2m_1dbaee3e_ce5f_437b_b54c_6804519e37e5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T22:10:19.257226+00:00
-- url     : https://prove2.me/submissions/79bc39a3-6441-4c36-98ad-45cedb79b7c4

import Theorems.Thm_WilliamsonShmoys_maximal_planar_augmentation__p2m_b05b2ac9_cf86_42cd_81eb_d15df4254060_a2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hConn : H.Connected)
    (hH : HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       letI : DecidableRel K.Adj := Classical.decRel K.Adj
       H.edgeFinset.card ≤ K.edgeFinset.card) :=
  WilliamsonShmoys.maximal_planar_augmentation__p2m_b05b2ac9_cf86_42cd_81eb_d15df4254060_a2 H hH hV