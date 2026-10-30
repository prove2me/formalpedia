-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_card_maximal_property_supergraph__p2m_eb929d3d_412f_49f7_ad86_3f0f4e3e928c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:49:39.928482+00:00
-- url     : https://prove2.me/submissions/c275d49b-83c6-496a-b8d7-eb52ff7c229d

import Mathlib
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] (T : SimpleGraph V)
    (P : SimpleGraph V → Prop) (hT : P T) :
    ∃ G : SimpleGraph V, T.edgeSet ⊆ G.edgeSet ∧ P G ∧
      ∀ H : SimpleGraph V, G.edgeSet ⊆ H.edgeSet → P H →
        ¬ Nat.card G.edgeSet < Nat.card H.edgeSet := by
  classical
  let Q : SimpleGraph V → Prop := fun G => T ≤ G ∧ P G
  obtain ⟨G, hDecG, hG⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists (p := Q)).2
      ⟨T, ⟨le_rfl, hT⟩⟩
  letI : DecidableRel G.Adj := hDecG
  refine ⟨G, ?_, hG.1.2, ?_⟩
  · exact SimpleGraph.edgeSet_subset_edgeSet.mpr hG.1.1
  · intro H hGH hPH
    have hle : Nat.card H.edgeSet ≤ Nat.card G.edgeSet := by
      simpa only [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet] using
        (hG.2 ⟨le_trans hG.1.1 (SimpleGraph.edgeSet_subset_edgeSet.mp hGH), hPH⟩)
    exact not_lt_of_ge hle