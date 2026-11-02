-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_disconnected_edge_bound__p2m_b11eb619_37a3_43a5_a612_72f4475984ba_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:27:49.902985+00:00
-- url     : https://prove2.me/submissions/b81a7f1f-ed7e-4117-8df9-80bfea2b481f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_2868a47b_b066_46c0_a57b_16dc6ed3b9ef_a2
import Theorems.Thm_WilliamsonShmoys_planar_connected_simple_graph_edge_bound__p2m_2868a47b_b066_46c0_a57b_16dc6ed3b9ef_a2
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : HasPlanarDrawingOn G) (hcard : 3 ≤ Fintype.card V) (hconn : ¬ G.Connected) :
    G.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  classical
  obtain ⟨H, hGH, hHconn, hHdraw⟩ :=
    WilliamsonShmoys.planar_drawing_connected_extension__p2m_2868a47b_b066_46c0_a57b_16dc6ed3b9ef_a2
      G hG hconn
  have hbound :=
    WilliamsonShmoys.planar_connected_simple_graph_edge_bound__p2m_2868a47b_b066_46c0_a57b_16dc6ed3b9ef_a2
      H hHdraw hcard hHconn
  have hmono : G.edgeFinset.card ≤ H.edgeFinset.card := by
    exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hGH)
  omega