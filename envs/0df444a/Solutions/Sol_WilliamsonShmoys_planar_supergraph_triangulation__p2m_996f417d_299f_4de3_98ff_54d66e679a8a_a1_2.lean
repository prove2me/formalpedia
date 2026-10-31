-- Prove2me | solution 2 for WilliamsonShmoys.planar_supergraph_triangulation__p2m_996f417d_299f_4de3_98ff_54d66e679a8a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:12:53.458655+00:00
-- url     : https://prove2.me/submissions/411b3974-fc9e-4de7-be56-6285002e3122

import Theorems.Thm_WilliamsonShmoys_planar_completion_edge_count_ff597491

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hV : 3 ≤ Fintype.card V) : ∃ W : SimpleGraph V, G ≤ W ∧ WilliamsonShmoys.HasPlanarDrawingOn W ∧ W.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.planar_completion_edge_count_ff597491 G hG hV
