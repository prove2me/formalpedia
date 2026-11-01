-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_card_upper_bound__p2m_ad845c85_bbc7_45e1_b337_b2f3a4b80492_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:04:44.241539+00:00
-- url     : https://prove2.me/submissions/c43d9057-7f72-48d9-b408-63cd16e200cb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation__p2m_01732aef_dd3e_4b78_a11c_771f0411d541_a1
import Theorems.Thm_WilliamsonShmoys_connected_planar_simple_graph_edge_card_upper_bound__p2m_01732aef_dd3e_4b78_a11c_771f0411d541_a1
import Theorems.Thm_WilliamsonShmoys_simple_graph_edgeFinset_card_mono__p2m_01732aef_dd3e_4b78_a11c_771f0411d541_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
      K.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  classical
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  obtain ⟨H, hKH, hHdraw, hHconn⟩ :=
    WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_01732aef_dd3e_4b78_a11c_771f0411d541_a1 K hK hcard
  have hHcard :
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
        H.edgeFinset.card ≤ 3 * Fintype.card V - 6) :=
    WilliamsonShmoys.connected_planar_simple_graph_edge_card_upper_bound__p2m_01732aef_dd3e_4b78_a11c_771f0411d541_a1 H hHdraw hHconn hcard
  exact le_trans
    (WilliamsonShmoys.simple_graph_edgeFinset_card_mono__p2m_01732aef_dd3e_4b78_a11c_771f0411d541_a1 K H hKH)
    hHcard