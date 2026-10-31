-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_simple_graph_edge_count__p2m_e546a1c1_10cc_476b_a894_225ced90c5fe_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:09:55.19054+00:00
-- url     : https://prove2.me/submissions/876664e9-af59-4e9a-9e9f-956ab94a49c8

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_count_equations__p2m_27a5cf8c_cedc_4abf_b82c_50a7768c797c_a2
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hG : HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V, G ≤ K → HasPlanarDrawingOn K → K = G) :
    G.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨f, heuler, htriangles⟩ :=
    WilliamsonShmoys.maximal_planar_face_count_equations__p2m_27a5cf8c_cedc_4abf_b82c_50a7768c797c_a2
      G hV hG hmax
  omega
