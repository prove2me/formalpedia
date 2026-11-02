-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_planar_supergraph_strict_extension__p2m_8335b04f_4e67_4cd5_9960_e59cc2d55a11_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T02:42:11.33998+00:00
-- url     : https://prove2.me/submissions/1ff75b4d-6c4f-4dfb-814b-6c360c950b8c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_extension_of_disconnected_drawing
import Theorems.Thm_SimpleGraphEdgeCardMonotone__p2m_cf08a975_8aa0_46e9_901e_a88c02c5eb25_a3

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V)
    (hV : 3 <= Fintype.card V) (hN : HasPlanarDrawingOn N)
    (hDisconnected : ¬ N.Connected) :
    ∃ K : SimpleGraph V, N <= K ∧ HasPlanarDrawingOn K ∧
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj
       letI : DecidableRel N.Adj := Classical.decRel N.Adj
       N.edgeFinset.card < K.edgeFinset.card) := by
  obtain ⟨K, hNK, hKnotN, hK⟩ :=
    WilliamsonShmoys.planar_edge_extension_of_disconnected_drawing
      N hN hV hDisconnected
  refine ⟨K, hNK, hK, ?_⟩
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  letI : DecidableRel N.Adj := Classical.decRel N.Adj
  have hNotBack : ¬ (∀ u v, K.Adj u v → N.Adj u v) := by
    intro hBack
    have hEq : K = N := le_antisymm hBack hNK
    exact hKnotN hEq
  exact
    (SimpleGraphEdgeCardMonotone__p2m_cf08a975_8aa0_46e9_901e_a88c02c5eb25_a3
      N K (by
        intro u v huv
        exact hNK huv)).2 hNotBack