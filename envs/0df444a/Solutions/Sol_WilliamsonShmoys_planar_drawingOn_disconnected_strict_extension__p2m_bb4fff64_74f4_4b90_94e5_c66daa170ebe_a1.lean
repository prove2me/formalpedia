-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_disconnected_strict_extension__p2m_bb4fff64_74f4_4b90_94e5_c66daa170ebe_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:42:27.966275+00:00
-- url     : https://prove2.me/submissions/5b7fd9db-a249-4a11-9cbb-adde51f4722c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_planar_supergraph__p2m_24055289_8edd_427c_8cf4_b86f3a2eaef9_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_connected__p2m_24055289_8edd_427c_8cf4_b86f3a2eaef9_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hDisconnected : ¬ M.Connected) :
    ∃ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet ∧
      ¬ N.edgeSet ⊆ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.finite_maximal_planar_supergraph__p2m_24055289_8edd_427c_8cf4_b86f3a2eaef9_a1 M hM
  have hNconnected : N.Connected :=
    WilliamsonShmoys.maximal_planar_graph_connected__p2m_24055289_8edd_427c_8cf4_b86f3a2eaef9_a1 N hN hmax
  have hneq : N ≠ M := by
    intro hEq
    apply hDisconnected
    rw [← hEq]
    exact hNconnected
  refine ⟨N, SimpleGraph.edgeSet_mono hMN, ?_, hN⟩
  intro hNM
  apply hneq
  exact le_antisymm ((SimpleGraph.edgeSet_subset_edgeSet).1 hNM) hMN