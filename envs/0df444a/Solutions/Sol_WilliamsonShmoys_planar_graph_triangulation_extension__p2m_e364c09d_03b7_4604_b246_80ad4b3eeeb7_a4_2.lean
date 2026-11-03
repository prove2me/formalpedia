-- Prove2me | solution 2 for WilliamsonShmoys.planar_graph_triangulation_extension__p2m_e364c09d_03b7_4604_b246_80ad4b3eeeb7_a4
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:46:22.930776+00:00
-- url     : https://prove2.me/submissions/a04d4d88-57b8-448c-96ed-381f2328f41e

import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_has_triangulation_edge_count__p2m_7f938502_4ebe_49de_af5d_b80801e1f743_a5

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hcard : 3 ≤ Fintype.card V) : ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ (letI : DecidableRel K.Adj := Classical.decRel K.Adj; K.edgeFinset.card + 6 = 3 * Fintype.card V) :=
  WilliamsonShmoys.planar_drawingOn_has_triangulation_edge_count__p2m_7f938502_4ebe_49de_af5d_b80801e1f743_a5 H hH hcard