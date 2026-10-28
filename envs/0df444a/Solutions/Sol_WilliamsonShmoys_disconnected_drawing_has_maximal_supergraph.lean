-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_drawing_has_maximal_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:51:46.823436+00:00
-- url     : https://prove2.me/submissions/bc8466b5-964d-4be6-ab28-3e93bb56b4a7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ J : SimpleGraph V, H ≤ J ∧
      WilliamsonShmoys.HasPlanarDrawingOn J ∧
      ∀ K : SimpleGraph V,
        J ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ J := by
  classical
  have key : ∀ (P : SimpleGraph V → Prop) (T : SimpleGraph V), P T →
      ∃ L, T ≤ L ∧ P L ∧ ∀ M, L ≤ M → P M → M = L := by
    intro P T hT
    have hfin : {L : SimpleGraph V | T ≤ L ∧ P L}.Finite := Set.toFinite _
    obtain ⟨L, hL, hmax⟩ := Set.exists_max_image {L : SimpleGraph V | T ≤ L ∧ P L}
      (fun L => L.edgeSet.ncard) hfin ⟨T, le_rfl, hT⟩
    refine ⟨L, hL.1, hL.2, ?_⟩
    intro M hLM hM
    have hc : M.edgeSet.ncard ≤ L.edgeSet.ncard := hmax M ⟨le_trans hL.1 hLM, hM⟩
    have hsub : L.edgeSet ⊆ M.edgeSet := SimpleGraph.edgeSet_mono hLM
    have hfM : M.edgeSet.Finite := Set.toFinite _
    have := Set.eq_of_subset_of_ncard_le hsub hc hfM
    exact (SimpleGraph.edgeSet_inj.mp this.symm)
  obtain ⟨L, hGL, hL, hm⟩ := key (fun L => WilliamsonShmoys.HasPlanarDrawingOn L) _ ‹WilliamsonShmoys.HasPlanarDrawingOn _›
  exact ⟨L, hGL, hL, fun N hLN hN => by rw [hm N hLN hN]⟩
