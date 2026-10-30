-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_augmentation_54a0e51c
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T13:55:19.499441+00:00
-- url     : https://prove2.me/submissions/699a0b8e-1e84-4a4e-be58-9fec0c0e875c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_54a0e51c_maximal_drawable_supergraph
import Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_54a0e51c_maximal_drawable_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcount : G.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ N : SimpleGraph V,
      G.edgeSet ⊆ N.edgeSet ∧
      ¬ N.edgeSet ⊆ G.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N := by
  obtain ⟨N, hGN, hN, hmax⟩ :=
    WilliamsonShmoys.planar_edge_augmentation_54a0e51c_maximal_drawable_supergraph G hG
  have hNcount :=
    WilliamsonShmoys.planar_edge_augmentation_54a0e51c_maximal_drawable_edge_count N hV hN hmax
  have hstrict : ¬ N.edgeSet ⊆ G.edgeSet := by
    intro hNG
    have heq : N.edgeSet = G.edgeSet := Set.Subset.antisymm hNG hGN
    rw [← heq] at hcount
    omega
  exact ⟨N, hGN, hstrict, hN⟩