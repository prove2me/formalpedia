-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_with_triangulated_edge_count__p2m_eba63f99_4b89_43c7_9979_04802f4e758b_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:55:50.744142+00:00
-- url     : https://prove2.me/submissions/4e0122e8-a23c-435c-8e87-7c76539c7bbf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_has_maximal_extension__p2m_7235810a_9787_44ff_bc97_6b6cda77c472_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_has_triangulated_edge_count__p2m_7235810a_9787_44ff_bc97_6b6cda77c472_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hU : HasPlanarDrawingOn U)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ W : SimpleGraph V, U ≤ W ∧ HasPlanarDrawingOn W ∧
      (letI : DecidableRel W.Adj := Classical.decRel W.Adj
       W.edgeFinset.card = 3 * Fintype.card V - 6) := by
  obtain ⟨W, hUW, hW, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_has_maximal_extension__p2m_7235810a_9787_44ff_bc97_6b6cda77c472_a1
      U hU
  refine ⟨W, hUW, hW, ?_⟩
  exact WilliamsonShmoys.maximal_planar_graph_has_triangulated_edge_count__p2m_7235810a_9787_44ff_bc97_6b6cda77c472_a1
    W hW hcard hmax