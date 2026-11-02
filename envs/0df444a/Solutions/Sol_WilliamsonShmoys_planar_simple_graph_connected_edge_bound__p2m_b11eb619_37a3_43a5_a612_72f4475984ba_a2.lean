-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_connected_edge_bound__p2m_b11eb619_37a3_43a5_a612_72f4475984ba_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:26:42.636869+00:00
-- url     : https://prove2.me/submissions/375b1ec1-b17e-4631-b709-2e4cdeab21b7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_6e84ab66_a241_4b3a_ab2e_bd91b32f8011_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_6e84ab66_a241_4b3a_ab2e_bd91b32f8011_a1
import Theorems.Thm_WilliamsonShmoys_simpleGraph_edgeFinset_card_mono__p2m_6e84ab66_a241_4b3a_ab2e_bd91b32f8011_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V)
    (hconn : G.Connected) :
    G.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  classical
  obtain ⟨H, hsub, hplanar, hHconn, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_6e84ab66_a241_4b3a_ab2e_bd91b32f8011_a1
      G hG hcard hconn
  have hmono :=
    WilliamsonShmoys.simpleGraph_edgeFinset_card_mono__p2m_6e84ab66_a241_4b3a_ab2e_bd91b32f8011_a1
      hsub
  have hbound :=
    WilliamsonShmoys.maximal_planar_edge_bound__p2m_6e84ab66_a241_4b3a_ab2e_bd91b32f8011_a1
      hplanar hcard hHconn hmax
  omega