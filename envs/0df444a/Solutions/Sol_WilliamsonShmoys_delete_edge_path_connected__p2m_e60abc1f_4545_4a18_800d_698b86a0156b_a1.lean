-- Prove2me | solution 1 for WilliamsonShmoys.delete_edge_path_connected__p2m_e60abc1f_4545_4a18_800d_698b86a0156b_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T17:57:44.399966+00:00
-- url     : https://prove2.me/submissions/9dc17a57-d764-4152-8e40-91c7fc2e014d

import Mathlib

set_option autoImplicit false
open SimpleGraph

theorem solution {V : Type} [Fintype V] [Nonempty V]
    (H : SimpleGraph V) (u v : V)
    (hconn : H.Connected)
    (hpath : (H.deleteEdges {s(u, v)}).Reachable u v) :
    (H.deleteEdges {s(u, v)}).Connected := by
  classical
  have hnotBridge : ¬ H.IsBridge s(u, v) := by
    intro hb
    exact (SimpleGraph.isBridge_iff.mp hb) hpath
  exact hconn.connected_delete_edge_of_not_isBridge hnotBridge
