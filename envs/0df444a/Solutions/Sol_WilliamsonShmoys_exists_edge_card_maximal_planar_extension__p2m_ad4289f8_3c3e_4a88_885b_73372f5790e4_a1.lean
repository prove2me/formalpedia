-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_card_maximal_planar_extension__p2m_ad4289f8_3c3e_4a88_885b_73372f5790e4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:17:50.85752+00:00
-- url     : https://prove2.me/submissions/84bb1ce1-e6c0-4945-a276-b474dc8873d3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    ∃ M : SimpleGraph V,
      H ≤ M ∧
      HasPlanarDrawingOn M ∧
      H.edgeFinset.card ≤ M.edgeFinset.card ∧
      ∀ N : SimpleGraph V, H ≤ N → HasPlanarDrawingOn N →
        N.edgeFinset.card ≤ M.edgeFinset.card := by
  classical
  let feasible : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => H ≤ G ∧ HasPlanarDrawingOn G
  have hH_feasible : H ∈ feasible := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨le_rfl, hH⟩⟩
  have feasible_nonempty : feasible.Nonempty := ⟨H, hH_feasible⟩
  let edgeCounts : Finset ℕ := feasible.image fun G => G.edgeFinset.card
  have edgeCounts_nonempty : edgeCounts.Nonempty := feasible_nonempty.image _
  let maxEdges : ℕ := edgeCounts.max' edgeCounts_nonempty
  have maxEdges_mem : maxEdges ∈ edgeCounts := by
    exact Finset.max'_mem edgeCounts edgeCounts_nonempty
  obtain ⟨M, hM_feasible, hM_card⟩ := Finset.mem_image.mp maxEdges_mem
  have hM : H ≤ M ∧ HasPlanarDrawingOn M :=
    (Finset.mem_filter.mp hM_feasible).2
  refine ⟨M, hM.1, hM.2, ?_, ?_⟩
  · calc
      H.edgeFinset.card ≤ maxEdges := by
        dsimp [maxEdges]
        exact Finset.le_max' edgeCounts _
          (Finset.mem_image.mpr ⟨H, hH_feasible, rfl⟩)
      _ = M.edgeFinset.card := hM_card.symm
  · intro N hHN hN
    have hN_feasible : N ∈ feasible := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hHN, hN⟩⟩
    have hN_count : N.edgeFinset.card ∈ edgeCounts :=
      Finset.mem_image.mpr ⟨N, hN_feasible, rfl⟩
    calc
      N.edgeFinset.card ≤ maxEdges := by
        dsimp [maxEdges]
        exact Finset.le_max' edgeCounts _ hN_count
      _ = M.edgeFinset.card := hM_card.symm