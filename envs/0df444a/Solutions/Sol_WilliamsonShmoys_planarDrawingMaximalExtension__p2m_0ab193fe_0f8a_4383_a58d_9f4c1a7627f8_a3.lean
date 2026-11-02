-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingMaximalExtension__p2m_0ab193fe_0f8a_4383_a58d_9f4c1a7627f8_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:12:37.91898+00:00
-- url     : https://prove2.me/submissions/1159ed4a-ae77-4453-ba5d-52f2ed1006fe

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : HasPlanarDrawingOn L)
    (hn : 3 ≤ Fintype.card V) :
    ∃ (M : SimpleGraph V) (dM : DecidableRel M.Adj),
      HasPlanarDrawingOn M ∧
      (letI : DecidableRel L.Adj := dL
       letI : DecidableRel M.Adj := dM
       L.edgeFinset ⊆ M.edgeFinset) ∧
      (∀ (N : SimpleGraph V) (dN : DecidableRel N.Adj),
        HasPlanarDrawingOn N →
        (letI : DecidableRel M.Adj := dM
         letI : DecidableRel N.Adj := dN
         M.edgeFinset ⊆ N.edgeFinset) →
        (letI : DecidableRel M.Adj := dM
         letI : DecidableRel N.Adj := dN
         N.edgeFinset ⊆ M.edgeFinset)) := by
  classical
  let p : SimpleGraph V → Prop := fun G => HasPlanarDrawingOn G ∧ L ≤ G
  obtain ⟨M, dM, hM⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists p).2 ⟨L, hL, le_rfl⟩
  refine ⟨M, dM, hM.1.1, ?_, ?_⟩
  · letI : DecidableRel L.Adj := dL
    letI : DecidableRel M.Adj := dM
    exact SimpleGraph.edgeFinset_subset_edgeFinset.2 hM.1.2
  · intro N dN hN hMN
    letI : DecidableRel M.Adj := dM
    letI : DecidableRel N.Adj := dN
    have hMN' : M ≤ N := SimpleGraph.edgeFinset_subset_edgeFinset.1 hMN
    have hNprop : p N := ⟨hN, hM.1.2.trans hMN'⟩
    have hcard : N.edgeFinset.card ≤ M.edgeFinset.card := hM.2 hNprop
    have heq : M.edgeFinset = N.edgeFinset := Finset.eq_of_subset_of_card_le hMN hcard
    exact heq.symm.subset