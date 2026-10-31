-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_triangulation__p2m_ecceac01_0239_445e_a0b3_a366a9290cdc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:54:02.321064+00:00
-- url     : https://prove2.me/submissions/45a09c6e-5623-4266-85d6-3da8670d4cb8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph__p2m_d0ea3fbd_f04a_4b41_b21e_1f15e29cc103_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_triangulation_edge_count__p2m_d0ea3fbd_f04a_4b41_b21e_1f15e29cc103_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hV : 3 <= Fintype.card V) :
    exists H : SimpleGraph V, G <= H /\ WilliamsonShmoys.HasPlanarDrawingOn H /\
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  apply Exists.elim
    (WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_d0ea3fbd_f04a_4b41_b21e_1f15e29cc103_a1
      G hDraw)
  intro H hh
  have hGH : G <= H := hh.1
  have hHDraw : WilliamsonShmoys.HasPlanarDrawingOn H := hh.2.1
  have hMax : forall K : SimpleGraph V, H <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = H := hh.2.2
  apply Exists.intro H
  exact And.intro hGH (And.intro hHDraw
    (WilliamsonShmoys.maximal_planar_drawing_has_triangulation_edge_count__p2m_d0ea3fbd_f04a_4b41_b21e_1f15e29cc103_a1
      H hHDraw hV hMax))