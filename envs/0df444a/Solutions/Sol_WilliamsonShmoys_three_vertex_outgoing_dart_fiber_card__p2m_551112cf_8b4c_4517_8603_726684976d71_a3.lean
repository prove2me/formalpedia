-- Prove2me | solution 1 for WilliamsonShmoys.three_vertex_outgoing_dart_fiber_card__p2m_551112cf_8b4c_4517_8603_726684976d71_a3
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:49:49.74976+00:00
-- url     : https://prove2.me/submissions/79d4ae6a-6017-47e7-b97c-4e227b60b8e1

import Theorems.Thm_WilliamsonShmoys_three_vertex_outgoing_dart_fiber_card__p2m_551112cf_8b4c_4517_8603_726684976d71_a4

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : Fintype.card V = 3)
    (hcomplete : ∀ u v : V, u ≠ v → H.Adj u v)
    [DecidableRel H.Adj]
    (v : V) :
    Fintype.card {d : H.Dart // d.fst = v} = 2 :=
  WilliamsonShmoys.three_vertex_outgoing_dart_fiber_card__p2m_551112cf_8b4c_4517_8603_726684976d71_a4 H hV hcomplete v
