-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_017fa3bd_a11a_42f0_a60e_fe3ebb157a5f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:39:05.531045+00:00
-- url     : https://prove2.me/submissions/d904cabe-2b8e-4e0e-8ed4-d5cadf0a547f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_d281349a_ec75_422c_85cf_c5e8df5de150_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hMmax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj;
     3 * Fintype.card V ≤ M.edgeFinset.card + 6) := by
  classical
  letI : DecidableRel M.Adj := Classical.decRel M.Adj
  obtain ⟨N, hMN, hN, hbound⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_d281349a_ec75_422c_85cf_c5e8df5de150_a1
      M hM hV
  have hNM : N ≤ M := hMmax N hMN hN
  have hEq : N = M := le_antisymm hNM hMN
  subst N
  exact hbound