-- Prove2me | solution 1 for WilliamsonShmoys.triangulated_supergraph_edge_bound__p2m_c3950eb8_41cb_4e65_a38c_065736da1c7d_a3
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T14:31:22.181248+00:00
-- url     : https://prove2.me/submissions/f54eec2f-2b34-4056-a844-21087d69735b

-- ID: d3634604-6d84-4b01-a257-7ac1759b320a | NAME: WilliamsonShmoys.triangulated_supergraph_edge_bound__p2m_c3950eb8_41cb_4e65_a38c_065736da1c7d_a3 | 未本地编译验证
import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : 3 ≤ Fintype.card V)
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (f : Nat)
    (hsub : ∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v)
    (hle : H.edgeFinset.card ≤ K.edgeFinset.card)
    (heuler : K.edgeFinset.card + 2 = Fintype.card V + f)
    (hfaces : 3 * f = 2 * K.edgeFinset.card) :
    H.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  omega
