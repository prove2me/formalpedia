-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension_for_edge_bound__p2m_e34a2546_c833_4430_ac36_3fbd756a8832_a5
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:35:27.28421+00:00
-- url     : https://prove2.me/submissions/e2b987a5-3554-4708-9467-2a63ab23beff

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    ∃ M : SimpleGraph V,
      G ≤ M ∧ HasPlanarDrawingOn M ∧
      (letI : DecidableRel G.Adj := Classical.decRel G.Adj;
       letI : DecidableRel M.Adj := Classical.decRel M.Adj;
       G.edgeFinset.card ≤ M.edgeFinset.card) ∧
      ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M := by
  classical
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter fun H => G ≤ H ∧ HasPlanarDrawingOn H
  have hGmem : G ∈ candidates := by
    simp [candidates, hG]
  obtain ⟨M, hMmem, hMmax⟩ :=
    Finset.exists_max_image candidates (fun H => H.edgeFinset.card) ⟨G, hGmem⟩
  have hMprops := (Finset.mem_filter.mp hMmem).2
  refine ⟨M, hMprops.1, hMprops.2, ?_, ?_⟩
  · exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hMprops.1)
  · intro N hMN hN
    by_contra hNM
    have hMNne : M ≠ N := by
      intro hEq
      subst N
      exact hNM le_rfl
    have hMNlt : M < N := lt_of_le_of_ne hMN hMNne
    have hGN : G ≤ N := le_trans hMprops.1 hMN
    have hNmem : N ∈ candidates := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hGN, hN⟩
    have hcardlt : M.edgeFinset.card < N.edgeFinset.card :=
      Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hMNlt)
    exact (not_le_of_gt hcardlt) (hMmax N hNmem)