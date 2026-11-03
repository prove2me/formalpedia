-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_bf2a6b94_c712_4371_81b2_f7600a9fcb4a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T16:10:09.479973+00:00
-- url     : https://prove2.me/submissions/2ea57234-05b7-49f2-8a66-3a048c15c307

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_euler_edge_count_e02108dc_5749_4b8c_85cc_e86e3f71cac7
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    3 * Fintype.card V - 6 = K.edgeSet.ncard := by
  have h := WilliamsonShmoys.maximal_drawable_graph_has_euler_edge_count_e02108dc_5749_4b8c_85cc_e86e3f71cac7
    K hK hCard (fun L hKL hL => le_of_eq (hMax L hKL hL))
  omega
