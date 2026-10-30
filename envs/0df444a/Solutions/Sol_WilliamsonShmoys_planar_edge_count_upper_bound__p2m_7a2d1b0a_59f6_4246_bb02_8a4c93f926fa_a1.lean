-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_7a2d1b0a_59f6_4246_bb02_8a4c93f926fa_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T06:26:09.924001+00:00
-- url     : https://prove2.me/submissions/98bfe031-b5d4-43b1-ae93-a9c5c814c737

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_bound__p2m_e1d36954_e3fe_4560_a783_a7db2e32f709_a9
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  classical
  let S : Finset (SimpleGraph V) := Finset.univ.filter fun H =>
    G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H
  have hS : S.Nonempty := by
    refine ⟨G, ?_⟩
    simp [S, hDraw]
  obtain ⟨M, hMmem, hMmax⟩ :=
    Finset.exists_max_image S (fun H => H.edgeSet.ncard) hS
  have hM : G ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M :=
    (Finset.mem_filter.mp hMmem).2
  have hMax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      N.edgeSet.ncard ≤ M.edgeSet.ncard := by
    intro N hMN hNDraw
    apply hMmax N
    simp [S, le_trans hM.1 hMN, hNDraw]
  have hBound :=
    WilliamsonShmoys.maximal_drawable_edge_bound__p2m_e1d36954_e3fe_4560_a783_a7db2e32f709_a9
      M hM.2 hCard hMax
  exact Nat.le_trans (Set.ncard_mono (SimpleGraph.edgeSet_mono hM.1)) hBound