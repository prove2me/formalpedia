-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_completion_edge_count__p2m_bb1eb53b_a90c_47ce_9dd0_93bdb2c805fc_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:42:05.179894+00:00
-- url     : https://prove2.me/submissions/c2fbb6d3-dfcb-48d5-98d0-6d1766b36f87
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_exact_edge_completion__p2m_f50c5ba3_05f2_43c3_89bd_241d63b96a26_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hY : HasPlanarDrawingOn Y)
    (hmax : ∀ Z : SimpleGraph V, Y ≤ Z → HasPlanarDrawingOn Z → Z ≤ Y)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel Y.Adj := Classical.decRel Y.Adj
     3 * Fintype.card V - 6 = Y.edgeFinset.card) := by
  classical
  obtain ⟨Z, hYZ, hZ, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_exact_edge_completion__p2m_f50c5ba3_05f2_43c3_89bd_241d63b96a26_a1
      Y hcard hY
  have hZY : Z ≤ Y := hmax Z hYZ hZ
  have hEq : Z = Y := le_antisymm hZY hYZ
  subst Z
  exact hcount