-- Prove2me | solution 1 for WilliamsonShmoys.finite_graph_maximal_extension__p2m_1743449e_70b2_453d_82e4_df1f7d1e75bd_a3
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T20:27:22.942391+00:00
-- url     : https://prove2.me/submissions/7f7f9919-c2be-4a16-a8a9-e545ddde0c06

import Mathlib

theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Q : SimpleGraph V → Prop) (hQ : Q G)
    (hstep : ∀ (K : SimpleGraph V),
      G.edgeSet ⊆ K.edgeSet → Q K → ¬ K.Connected →
      ∃ L : SimpleGraph V, K.edgeSet ⊂ L.edgeSet ∧ Q L) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧ Q H ∧ H.Connected := by
  classical
  let p : SimpleGraph V → Prop :=
    fun H => G.edgeSet ⊆ H.edgeSet ∧ Q H
  have hpG : p G := ⟨by intro e he; exact he, hQ⟩
  obtain ⟨H, _hGH, hmax⟩ :=
    (Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := G) hpG)
  rcases hmax with ⟨hpH, hmax'⟩
  by_cases hc : H.Connected
  · exact ⟨H, hpH.1, hpH.2, hc⟩
  · exfalso
    obtain ⟨L, hss, hQL⟩ := hstep H hpH.1 hpH.2 hc
    have hHL : H ≤ L := SimpleGraph.edgeSet_subset_edgeSet.mp hss.1
    have hpL : p L := ⟨fun e he => hss.1 (hpH.1 he), hQL⟩
    have hLH : L ≤ H := hmax' hpL hHL
    exact hss.2 (SimpleGraph.edgeSet_subset_edgeSet.mpr hLH)
