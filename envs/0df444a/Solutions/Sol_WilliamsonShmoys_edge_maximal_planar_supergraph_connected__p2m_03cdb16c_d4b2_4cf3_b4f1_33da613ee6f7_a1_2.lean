-- Prove2me | solution 2 for WilliamsonShmoys.edge_maximal_planar_supergraph_connected__p2m_03cdb16c_d4b2_4cf3_b4f1_33da613ee6f7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:15:19.331878+00:00
-- url     : https://prove2.me/submissions/ade8c6e5-f0aa-4916-86fe-09a46be3042c

import Theorems.Thm_WilliamsonShmoys_disconnected_planar_supergraph_strict_extension__p2m_8335b04f_4e67_4cd5_9960_e59cc2d55a11_a3
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : HasPlanarDrawingOn M) (hMN : M <= N)
    (hN : HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V, M <= K -> HasPlanarDrawingOn K ->
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj
       letI : DecidableRel N.Adj := Classical.decRel N.Adj
       K.edgeFinset.card <= N.edgeFinset.card)) :
    N.Connected := by
  classical
  by_contra hDisconnected
  obtain ⟨K, hNK, hK, hCard⟩ :=
    WilliamsonShmoys.disconnected_planar_supergraph_strict_extension__p2m_8335b04f_4e67_4cd5_9960_e59cc2d55a11_a3
      N hV hN hDisconnected
  have hMK : M <= K := le_trans hMN hNK
  have hBound := hmax K hMK hK
  exact (not_le_of_gt hCard) hBound