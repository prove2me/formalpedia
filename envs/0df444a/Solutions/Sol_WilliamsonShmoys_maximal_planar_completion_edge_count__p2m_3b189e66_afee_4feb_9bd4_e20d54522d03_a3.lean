-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_completion_edge_count__p2m_3b189e66_afee_4feb_9bd4_e20d54522d03_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:24:45.85787+00:00
-- url     : https://prove2.me/submissions/f90e29ca-2d6d-4e3a-863b-653360daaead

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_extension__p2m_af412bdb_08d3_443e_9526_1f4e854292c2_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_af412bdb_08d3_443e_9526_1f4e854292c2_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      (letI : DecidableRel M.Adj := Classical.decRel M.Adj
       M.edgeFinset.card = 3 * Fintype.card V - 6) := by
  obtain ⟨M, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_af412bdb_08d3_443e_9526_1f4e854292c2_a1 L hL
  refine ⟨M, hLM, hM, ?_⟩
  exact WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_af412bdb_08d3_443e_9526_1f4e854292c2_a1 M hV hM hmax