-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_count__p2m_5d494874_3848_4892_940c_cf6b084398e7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:18:29.81501+00:00
-- url     : https://prove2.me/submissions/8efb982a-d56e-4f26-8f03-831503b190ca

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_connected_edge_card_lower_bound__p2m_a78a6ebd_f14e_4d5e_887a_7bf11c56fcc6_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected) :
    ∃ f : ℕ, Fintype.card V + f = H.edgeFinset.card + 2 := by
  have hcard : Fintype.card V ≤ H.edgeFinset.card + 1 :=
    WilliamsonShmoys.connected_edge_card_lower_bound__p2m_a78a6ebd_f14e_4d5e_887a_7bf11c56fcc6_a1 H hconn
  refine ⟨(H.edgeFinset.card + 2) - Fintype.card V, ?_⟩
  omega