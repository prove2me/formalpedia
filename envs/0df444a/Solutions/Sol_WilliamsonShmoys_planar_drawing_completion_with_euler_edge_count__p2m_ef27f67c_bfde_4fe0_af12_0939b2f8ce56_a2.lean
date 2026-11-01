-- Prove2me | solution 1 for WilliamsonShmoys_planar_drawing_completion_with_euler_edge_count__p2m_ef27f67c_bfde_4fe0_af12_0939b2f8ce56_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:19:41.277422+00:00
-- url     : https://prove2.me/submissions/c88d0a7a-57ea-4468-8267-d506ee6adab6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_extend_planar_graph_to_inclusion_maximal__p2m_b372cfef_764e_41b9_a3f0_cf4f0282f71c_a2
import Theorems.Thm_WilliamsonShmoys_inclusion_maximal_planar_graph_has_euler_edge_count__p2m_b372cfef_764e_41b9_a3f0_cf4f0282f71c_a2
import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    Exists fun (L : SimpleGraph V) => Exists fun (dL : DecidableRel L.Adj) =>
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      G.edgeFinset ⊆ L.edgeFinset ∧
      L.edgeFinset.card = 3 * Fintype.card V - 6 := by
  obtain ⟨L, dL, hL, hGL, hmax⟩ :=
    WilliamsonShmoys_extend_planar_graph_to_inclusion_maximal__p2m_b372cfef_764e_41b9_a3f0_cf4f0282f71c_a2 G dG hG
  exact ⟨L, dL, hL, hGL,
    WilliamsonShmoys_inclusion_maximal_planar_graph_has_euler_edge_count__p2m_b372cfef_764e_41b9_a3f0_cf4f0282f71c_a2 L dL hL hcard hmax⟩