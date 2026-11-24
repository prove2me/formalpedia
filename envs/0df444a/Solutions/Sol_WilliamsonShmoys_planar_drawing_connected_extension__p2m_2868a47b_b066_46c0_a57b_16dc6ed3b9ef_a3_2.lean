-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_connected_extension__p2m_2868a47b_b066_46c0_a57b_16dc6ed3b9ef_a3
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:47:41.280456+00:00
-- url     : https://prove2.me/submissions/9f9a371b-73fc-4bff-b931-769a92f7dc79

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_connected
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_planar_edge_extension_of_disconnected_drawing
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extension_for_edge_bound_ef555edc

set_option autoImplicit false
open WilliamsonShmoys
open scoped BigOperators

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : HasPlanarDrawingOn G) (hcard : 3 ≤ Fintype.card V) (hconn : ¬ G.Connected) : ∃ H : SimpleGraph V, G ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H := by
  obtain ⟨H0, hGH0, hH0, hle0, hMax0⟩ := WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_bound_ef555edc G hG
  have hC0 : H0.Connected := WilliamsonShmoys.maximal_planar_drawingOn_connected H0 hH0 hMax0 hcard
  exact ⟨H0, hGH0, hC0, hH0⟩
