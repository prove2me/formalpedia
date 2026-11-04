-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawable_supergraph_edge_bound__p2m_57c283a7_68a4_4e3d_813f_6e392f4dfebc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-04T02:31:50.003705+00:00
-- url     : https://prove2.me/submissions/d94b0c6a-9b87-4db7-aa6f-55d190ee7767

import Theorems.Thm_WilliamsonShmoys_planar_drawing_augmentation_maximal_extension__p2m_0835c3dc_b66c_4223_9284_2bc5bd7f2cf4_a2
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_edge_bound__p2m_16f13def_1905_44d4_887c_a7f874e9f4a3_a3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V, HasPlanarDrawingOn N ∧ M ≤ N ∧
      ∀ [DecidableRel N.Adj], 3 * Fintype.card V - 6 ≤ N.edgeFinset.card := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_augmentation_maximal_extension__p2m_0835c3dc_b66c_4223_9284_2bc5bd7f2cf4_a2 M hM
  have hmax' : ∀ K : SimpleGraph V,
      (∀ u v, N.Adj u v → K.Adj u v) →
      HasPlanarDrawingOn K → ∀ u v, K.Adj u v → N.Adj u v := by
    intro K hNK hK u v huv
    have hle : N ≤ K := by
      intro a b hab
      exact hNK a b hab
    exact hmax K hle hK huv
  refine ⟨N, hN, hMN, ?_⟩
  intro inst
  have heq : (letI : DecidableRel N.Adj := Classical.decRel N.Adj
      N.edgeFinset) = N.edgeFinset := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
  have hb := WilliamsonShmoys.maximal_drawable_supergraph_edge_bound__p2m_16f13def_1905_44d4_887c_a7f874e9f4a3_a3 N hcard hN hmax'
  change 3 * Fintype.card V - 6 ≤
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj
     N.edgeFinset).card at hb
  rw [heq] at hb
  exact hb
