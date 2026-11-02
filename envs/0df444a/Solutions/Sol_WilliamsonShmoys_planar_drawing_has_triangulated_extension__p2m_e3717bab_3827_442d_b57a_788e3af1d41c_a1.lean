-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_triangulated_extension__p2m_e3717bab_3827_442d_b57a_788e3af1d41c_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:14:38.366939+00:00
-- url     : https://prove2.me/submissions/4836611b-fb6a-4241-954d-d597f0b30f03
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension__p2m_67db8130_6ce9_48ac_b689_e2c8fddc3a6e_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_67db8130_6ce9_48ac_b689_e2c8fddc3a6e_a2
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V, M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      (letI : DecidableRel N.Adj := Classical.decRel N.Adj
       N.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_extension__p2m_67db8130_6ce9_48ac_b689_e2c8fddc3a6e_a2
      M hM hcard
  refine ⟨N, hMN, hN, ?_⟩
  exact WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_67db8130_6ce9_48ac_b689_e2c8fddc3a6e_a2
    N hN hcard hmax