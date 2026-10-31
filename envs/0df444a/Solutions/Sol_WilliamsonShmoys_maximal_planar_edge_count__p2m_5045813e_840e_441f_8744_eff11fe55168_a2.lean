-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_5045813e_840e_441f_8744_eff11fe55168_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:51:34.558852+00:00
-- url     : https://prove2.me/submissions/7c1c682e-eee3-4da2-aca0-d45a70d3ee46

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawable_edge_count_upper__p2m_8e3b1f8a_4617_463b_ae07_33ab92d25c24_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_8e3b1f8a_4617_463b_ae07_33ab92d25c24_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hDraw : HasPlanarDrawingOn K)
    (hMax : forall L : SimpleGraph V, K <= L -> HasPlanarDrawingOn L -> L = K)
    (hCard : 3 <= Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.planar_drawable_edge_count_upper__p2m_8e3b1f8a_4617_463b_ae07_33ab92d25c24_a1 K hDraw hCard
  have hLower := WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_8e3b1f8a_4617_463b_ae07_33ab92d25c24_a1 K hDraw hMax hCard
  omega