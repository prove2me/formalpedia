-- Prove2me | solution 1 for WilliamsonShmoys.iterate_edge_extensions__p2m_8875bb45_86a4_4d7c_b2ea_8d56d84fd5c3_a1
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-11T13:56:07.9145+00:00
-- url     : https://prove2.me/submissions/897d15cc-0933-4820-a681-9933bed91e9f

import Mathlib

set_option autoImplicit false

/-- Iterating edge extensions eventually makes a graph connected, preserving the property. -/
theorem solution {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (K : SimpleGraph V)
    (hK : P K)
    (hStep : ∀ (G : SimpleGraph V), P G → ¬ G.Connected →
      ∃ u v : V,
        u ≠ v ∧ ¬ G.Reachable u v ∧ ¬ G.Adj u v ∧
        P (G ⊔ SimpleGraph.fromRel (fun x y : V => x = u ∧ y = v)))
    (hDisconnected : ¬ K.Connected) :
    ∃ H : SimpleGraph V, K ≤ H ∧ H.Connected ∧ P H := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun H : SimpleGraph V => K ≤ H ∧ P H)
  have hS : S.Nonempty := ⟨K, by simp [S, hK]⟩
  obtain ⟨H, hHS, hmax⟩ :=
    Finset.exists_max_image S (fun H : SimpleGraph V => H.edgeSet.ncard) hS
  have hKH : K ≤ H := (Finset.mem_filter.mp hHS).2.1
  have hPH : P H := (Finset.mem_filter.mp hHS).2.2
  refine ⟨H, hKH, ?_, hPH⟩
  by_contra hHconn
  obtain ⟨u, v, hne, hnreach, hnadj, hP'⟩ := hStep H hPH hHconn
  let H' : SimpleGraph V := H ⊔ SimpleGraph.fromRel (fun x y : V => x = u ∧ y = v)
  have hHH' : H ≤ H' := le_sup_left
  have hH'mem : H' ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hKH.trans hHH', hP'⟩
  have hle : H'.edgeSet.ncard ≤ H.edgeSet.ncard := hmax H' hH'mem
  have hedge_in : s(u, v) ∈ H'.edgeSet := by
    change s(u, v) ∈ (H ⊔ SimpleGraph.fromRel (fun x y : V => x = u ∧ y = v)).edgeSet
    rw [SimpleGraph.mem_edgeSet, SimpleGraph.sup_adj]
    right
    rw [SimpleGraph.fromRel_adj]
    exact ⟨hne, Or.inl ⟨rfl, rfl⟩⟩
  have hedge_notin : s(u, v) ∉ H.edgeSet := by
    rw [SimpleGraph.mem_edgeSet]
    exact hnadj
  have hssub : H.edgeSet ⊂ H'.edgeSet := by
    rw [Set.ssubset_iff_subset_ne]
    refine ⟨SimpleGraph.edgeSet_mono hHH', ?_⟩
    intro heq
    exact hedge_notin (heq ▸ hedge_in)
  have hlt : H.edgeSet.ncard < H'.edgeSet.ncard :=
    Set.ncard_lt_ncard hssub (Set.toFinite H'.edgeSet)
  omega
