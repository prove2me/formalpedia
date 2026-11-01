-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph_exists__p2m_cc6eda38_1b75_4537_8542_c84b46a8d9a9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:56:20.566034+00:00
-- url     : https://prove2.me/submissions/a6d4ae89-e79a-4441-9372-49e18cfbb9bc

import Theorems.Thm_WilliamsonShmoys_finite_simple_graph_set_has_maximal_member__p2m_e1cd0124_e641_4ece_baff_4e3ebf9bbef8_a1

set_option autoImplicit false

open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ L : SimpleGraph V, H ≤ L →
        WilliamsonShmoys.HasPlanarDrawingOn L → L = H := by
  classical
  let S : Set (SimpleGraph V) :=
    {L | K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L}
  have hS : S.Nonempty := ⟨K, le_rfl, hK⟩
  obtain ⟨H, hH, hmax⟩ :=
    WilliamsonShmoys.finite_simple_graph_set_has_maximal_member__p2m_e1cd0124_e641_4ece_baff_4e3ebf9bbef8_a1 S hS
  refine ⟨H, hH.1, hH.2, ?_⟩
  intro L hHL hPlanar
  have hL : L ∈ S := ⟨le_trans hH.1 hHL, hPlanar⟩
  exact le_antisymm (hmax L hL hHL) hHL