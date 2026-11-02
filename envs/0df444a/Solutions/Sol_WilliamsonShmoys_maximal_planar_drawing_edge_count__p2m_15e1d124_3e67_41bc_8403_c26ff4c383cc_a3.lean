-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_15e1d124_3e67_41bc_8403_c26ff4c383cc_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:59:43.298255+00:00
-- url     : https://prove2.me/submissions/5c6fe659-e7a3-45c8-a795-d1207a842775
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_triangulation_extension__p2m_9358304e_f36c_4627_ac4a_68d95a8f78e3_a2
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj
     M.edgeFinset.card = 3 * Fintype.card V - 6) := by
  classical
  obtain ⟨N, hMN, hN, hcount⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_triangulation_extension__p2m_9358304e_f36c_4627_ac4a_68d95a8f78e3_a2
      M hcard hM
  have hNM : N ≤ M := hmax N hMN hN
  have hEq : N = M := le_antisymm hNM hMN
  subst N
  exact hcount