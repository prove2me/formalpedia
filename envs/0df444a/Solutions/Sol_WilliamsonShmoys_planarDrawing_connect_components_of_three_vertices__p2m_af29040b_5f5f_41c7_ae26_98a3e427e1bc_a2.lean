-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawing_connect_components_of_three_vertices__p2m_af29040b_5f5f_41c7_ae26_98a3e427e1bc_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T00:37:31.19898+00:00
-- url     : https://prove2.me/submissions/a178ca7d-a856-4211-96b2-f16ab7141e4a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation_with_three_vertices
import Theorems.Thm_WilliamsonShmoys_simpleGraph_edgeFinset_card_mono__p2m_6e84ab66_a241_4b3a_ab2e_bd91b32f8011_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      G ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H ∧
        (letI : DecidableRel G.Adj := dG
         letI : DecidableRel H.Adj := dH
         G.edgeFinset.card ≤ H.edgeFinset.card) := by
  classical
  obtain ⟨H, hGH, hconn, hdraw, _hEdges⟩ :=
    WilliamsonShmoys.planar_drawing_connected_augmentation_with_three_vertices
      G hG hcard
  let dH : DecidableRel H.Adj := Classical.decRel H.Adj
  refine ⟨H, dH, hGH, hconn, hdraw, ?_⟩
  letI : DecidableRel G.Adj := dG
  letI : DecidableRel H.Adj := dH
  exact WilliamsonShmoys.simpleGraph_edgeFinset_card_mono__p2m_6e84ab66_a241_4b3a_ab2e_bd91b32f8011_a1 hGH