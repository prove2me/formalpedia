-- Prove2me | solution 1 for WilliamsonShmoys.finite_graph_extension_iteration__p2m_890a21e4_ea5b_4fa2_834e_277ff81160e9_a1
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-11T15:12:47.611121+00:00
-- url     : https://prove2.me/submissions/86a70d43-c1a2-4127-bc71-cbee1189e6b8

import Mathlib

set_option autoImplicit false

/-- Iterating edge extensions eventually yields a connected supergraph satisfying the property. -/
theorem solution {V : Type} [Fintype V]
    (G : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P G)
    (hstep : ∀ (K : SimpleGraph V),
      G.edgeSet ⊆ K.edgeSet →
      P K →
      ¬ K.Connected →
      ∃ L : SimpleGraph V,
        K.edgeSet ⊆ L.edgeSet ∧
        (∃ u v, ¬ K.Reachable u v ∧ L.Adj u v) ∧
        P L) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧ H.Connected ∧ P H := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun H : SimpleGraph V => G.edgeSet ⊆ H.edgeSet ∧ P H)
  have hS : S.Nonempty := ⟨G, by simp [S, hP]⟩
  obtain ⟨H, hHS, hmax⟩ :=
    Finset.exists_max_image S (fun H : SimpleGraph V => H.edgeSet.ncard) hS
  have hGH : G.edgeSet ⊆ H.edgeSet := (Finset.mem_filter.mp hHS).2.1
  have hPH : P H := (Finset.mem_filter.mp hHS).2.2
  refine ⟨H, hGH, ?_, hPH⟩
  by_contra hHconn
  obtain ⟨L, hHL, ⟨u, v, hnreach, hLadj⟩, hPL⟩ := hstep H hGH hPH hHconn
  have hLmem : L ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hGH.trans hHL, hPL⟩
  have hle : L.edgeSet.ncard ≤ H.edgeSet.ncard := hmax L hLmem
  have hedge_in : s(u, v) ∈ L.edgeSet := (SimpleGraph.mem_edgeSet L).mpr hLadj
  have hedge_notin : s(u, v) ∉ H.edgeSet := by
    rw [SimpleGraph.mem_edgeSet]
    intro h
    exact hnreach h.reachable
  have hssub : H.edgeSet ⊂ L.edgeSet := by
    rw [Set.ssubset_iff_subset_ne]
    exact ⟨hHL, fun heq => hedge_notin (heq ▸ hedge_in)⟩
  have hlt : H.edgeSet.ncard < L.edgeSet.ncard :=
    Set.ncard_lt_ncard hssub (Set.toFinite L.edgeSet)
  omega
