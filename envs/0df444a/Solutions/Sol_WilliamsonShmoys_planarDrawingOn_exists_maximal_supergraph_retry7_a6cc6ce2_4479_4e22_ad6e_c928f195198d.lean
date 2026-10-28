-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_exists_maximal_supergraph_retry7_a6cc6ce2_4479_4e22_ad6e_c928f195198d
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:51:42.417604+00:00
-- url     : https://prove2.me/submissions/990e412e-2ca5-43b0-8536-44b69a89f0cf

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    Exists (fun M : SimpleGraph V =>
      And (LE.le K M)
        (And (WilliamsonShmoys.HasPlanarDrawingOn M)
          (forall N : SimpleGraph V, LE.le M N ->
            WilliamsonShmoys.HasPlanarDrawingOn N -> LE.le N M))) := by
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
