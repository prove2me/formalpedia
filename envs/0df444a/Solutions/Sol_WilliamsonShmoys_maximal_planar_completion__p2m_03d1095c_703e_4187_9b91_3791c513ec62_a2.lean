-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_completion__p2m_03d1095c_703e_4187_9b91_3791c513ec62_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:28:22.051327+00:00
-- url     : https://prove2.me/submissions/d1c7a6d3-0523-4620-a78f-a028d3ed0888
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_completion_maximal_extension__p2m_bb1eb53b_a90c_47ce_9dd0_93bdb2c805fc_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_completion_edge_count__p2m_bb1eb53b_a90c_47ce_9dd0_93bdb2c805fc_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hX : HasPlanarDrawingOn X)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ Y : SimpleGraph V, X ≤ Y ∧ HasPlanarDrawingOn Y ∧
      (letI : DecidableRel Y.Adj := Classical.decRel Y.Adj
       3 * Fintype.card V - 6 = Y.edgeFinset.card) := by
  classical
  obtain ⟨Y, hXY, hY, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_completion_maximal_extension__p2m_bb1eb53b_a90c_47ce_9dd0_93bdb2c805fc_a1 X hX
  have hcount :=
    WilliamsonShmoys.maximal_planar_completion_edge_count__p2m_bb1eb53b_a90c_47ce_9dd0_93bdb2c805fc_a1 Y hY hmax hcard
  exact ⟨Y, hXY, hY, hcount⟩