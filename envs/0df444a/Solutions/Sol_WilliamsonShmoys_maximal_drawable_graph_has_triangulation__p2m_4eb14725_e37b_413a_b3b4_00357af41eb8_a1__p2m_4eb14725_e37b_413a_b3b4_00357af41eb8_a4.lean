-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_has_triangulation__p2m_4eb14725_e37b_413a_b3b4_00357af41eb8_a1__p2m_4eb14725_e37b_413a_b3b4_00357af41eb8_a4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:01:59.22703+00:00
-- url     : https://prove2.me/submissions/97e00a18-5ce0-45cc-8ca3-067c81a33fc1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_maximal_extension__p2m_637d8540_4fa2_4bdf_8eaf_997caf9c33c1_a2
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_triangulated_edge_count__p2m_637d8540_4fa2_4bdf_8eaf_997caf9c33c1_a2

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) [DecidableRel N.Adj] (hcard : 3 ≤ Fintype.card V) (hN : HasPlanarDrawingOn N) : ∃ (P : SimpleGraph V), N ≤ P ∧ HasPlanarDrawingOn P ∧ (∀ [DecidableRel P.Adj], P.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  classical
  obtain ⟨P, hNP, hP, hmax⟩ := WilliamsonShmoys.drawable_graph_has_maximal_extension__p2m_637d8540_4fa2_4bdf_8eaf_997caf9c33c1_a2 N hN
  refine ⟨P, hNP, hP, ?_⟩
  intro inst
  exact WilliamsonShmoys.maximal_drawable_graph_has_triangulated_edge_count__p2m_637d8540_4fa2_4bdf_8eaf_997caf9c33c1_a2 P hcard hP hmax