-- Prove2me | solution 2 for WilliamsonShmoys.planar_graph_triangulation_extension__p2m_a4df0ed7_7cc8_4f60_8566_0ad346baef91_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:18:34.056063+00:00
-- url     : https://prove2.me/submissions/a792c0a9-a5b0-4b34-aa1c-26fd593c0bff

import Theorems.Thm_WilliamsonShmoys_planar_completion_edge_count_for_maximal_edge_lower_bound
import Mathlib

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      N.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_completion_edge_count_for_maximal_edge_lower_bound N hcard hN
