-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_supergraph_exists__p2m_63ad9a14_da0c_4363_acd0_29ef03d610e6_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:55:19.022735+00:00
-- url     : https://prove2.me/submissions/a95415fe-20a3-47cb-8c44-bff9458575b6

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ (M : SimpleGraph V) (dM : DecidableRel M.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      L ≤ M ∧
      (∀ N : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn N →
        M ≤ N →
        N = M) := by
  classical
  let p : SimpleGraph V → Prop := fun G =>
    WilliamsonShmoys.HasPlanarDrawingOn G ∧ L ≤ G
  have hp : ∃ G : SimpleGraph V, p G := ⟨L, hL, le_rfl⟩
  obtain ⟨M, dM, hM⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists p).2 hp
  refine ⟨M, dM, hM.1.1, hM.1.2, ?_⟩
  intro N hN hMN
  have hsub : M.edgeFinset ⊆ N.edgeFinset :=
    SimpleGraph.edgeFinset_subset_edgeFinset.2 hMN
  have hLN : L ≤ N := le_trans hM.1.2 hMN
  have hcard : N.edgeFinset.card ≤ M.edgeFinset.card :=
    hM.2 ⟨hN, hLN⟩
  have heq : M.edgeFinset = N.edgeFinset :=
    Finset.eq_of_subset_of_card_le hsub hcard
  exact SimpleGraph.edgeFinset_inj.mp heq.symm