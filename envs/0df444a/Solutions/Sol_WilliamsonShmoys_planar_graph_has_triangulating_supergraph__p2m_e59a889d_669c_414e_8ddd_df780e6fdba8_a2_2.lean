-- Prove2me | solution 2 for WilliamsonShmoys.planar_graph_has_triangulating_supergraph__p2m_e59a889d_669c_414e_8ddd_df780e6fdba8_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:47:47.960803+00:00
-- url     : https://prove2.me/submissions/109b376f-28d9-4818-9f4c-54d0479fa42d

import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_supergraph

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (Y : SimpleGraph V) (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) (hV : 3 ≤ Fintype.card V) : ∃ Z : SimpleGraph V, Y ≤ Z ∧ WilliamsonShmoys.HasPlanarDrawingOn Z ∧ Z.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_has_triangulated_supergraph Y hY hV
