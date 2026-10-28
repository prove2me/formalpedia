-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_local_growth_implies_connected
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T15:11:08.828948+00:00
-- url     : https://prove2.me/submissions/065ef685-419a-4fe8-b1de-27a948ebd1f1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hGrow : ∀ G : SimpleGraph V, K ≤ G →
      WilliamsonShmoys.HasPlanarDrawingOn G → ¬ G.Connected →
      ∃ G' : SimpleGraph V, G ≤ G' ∧
        WilliamsonShmoys.HasPlanarDrawingOn G' ∧
        G.edgeSet.ncard < G'.edgeSet.ncard) :
    ∃ H : SimpleGraph V, K ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.Connected ∧
      K.edgeSet.ncard ≤ H.edgeSet.ncard := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun X0 : SimpleGraph V => K ≤ X0 ∧ WilliamsonShmoys.HasPlanarDrawingOn X0)).exists_max_image
    (fun X0 => X0.edgeFinset.card) ⟨K, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hK⟩⟩
  obtain ⟨hPQ, hQ⟩ : K ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
  have hc : ∀ X : SimpleGraph V, X.edgeSet.ncard = X.edgeFinset.card := fun X => by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  refine ⟨Q, hPQ, hQ, ?_, Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hPQ) (Set.toFinite _)⟩
  by_contra hnc
  obtain ⟨G', hQG, hG', hlt⟩ := hGrow Q hPQ hQ hnc
  have := hmax G' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ.trans hQG, hG'⟩)
  rw [hc, hc] at hlt
  omega
