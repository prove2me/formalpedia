-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_decomposition_for_edge_count_6274f47d_124c_4fd1_84e6_71540a951a1f
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T07:48:03.097688+00:00
-- url     : https://prove2.me/submissions/f996404e-4410-4757-aff8-b5b9c323fd42

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper_bound
import Theorems.Thm_WilliamsonShmoys_planar_graph_edge_augmentation_for_maximal_face_decomposition_6274f47d

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M = L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = L.edgeSet.ncard + 2 ∧
      3 * f = 2 * L.edgeSet.ncard := by
  have hUpper :=
    WilliamsonShmoys.maximal_planar_edge_count_upper_bound L hL hCard
  have hNotSmall : ¬ L.edgeSet.ncard < 3 * Fintype.card V - 6 := by
    intro hSmall
    obtain ⟨M, hStrict, hMDrawing⟩ :=
      WilliamsonShmoys.planar_graph_edge_augmentation_for_maximal_face_decomposition_6274f47d
        L hL hCard hSmall
    have hEq := hMax M hStrict.1 hMDrawing
    exact hStrict.2 (by simpa [hEq])
  have hEdges : L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
    omega
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega