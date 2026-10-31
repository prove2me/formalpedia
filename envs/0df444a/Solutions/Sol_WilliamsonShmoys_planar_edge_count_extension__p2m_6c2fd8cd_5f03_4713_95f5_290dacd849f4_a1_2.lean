-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_count_extension__p2m_6c2fd8cd_5f03_4713_95f5_290dacd849f4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:00:48.754395+00:00
-- url     : https://prove2.me/submissions/69f16a78-ef6e-4190-adf0-797edd491ceb

import Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_maximal_edge_count__p2m_d65752b0_c280_4c98_926b_0ae69c395723_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) (hN : HasPlanarDrawingOn N) (hV : 3 ≤ Fintype.card V) : ∃ K : SimpleGraph V, N ≤ K ∧ HasPlanarDrawingOn K ∧ K.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.planar_supergraph_with_maximal_edge_count__p2m_d65752b0_c280_4c98_926b_0ae69c395723_a1 N hN hV
