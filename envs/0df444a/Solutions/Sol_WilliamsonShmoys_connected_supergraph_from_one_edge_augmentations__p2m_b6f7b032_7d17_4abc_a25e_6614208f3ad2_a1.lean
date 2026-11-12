-- Prove2me | solution 1 for WilliamsonShmoys.connected_supergraph_from_one_edge_augmentations__p2m_b6f7b032_7d17_4abc_a25e_6614208f3ad2_a1
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-11T15:14:53.668263+00:00
-- url     : https://prove2.me/submissions/fa83decf-ddce-4f57-97bb-657b6d89c528

import Mathlib

set_option autoImplicit false

/-- Iterating one-edge augmentations from a property-satisfying graph reaches a connected one. -/
theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (hstep : ∀ (G : SimpleGraph V), P G → ¬ G.Connected →
      ∃ a b : V, ∃ H : SimpleGraph V,
        ¬ G.Adj a b ∧ ¬ G.Reachable a b ∧
        (∀ u v, H.Adj u v ↔
          G.Adj u v ∨ (u = a ∧ v = b) ∨ (u = b ∧ v = a)) ∧
        P H)
    (K : SimpleGraph V)
    (hK : P K) :
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
  by_contra hconn
  obtain ⟨a, b, L, hnadj, hnreach, hadj, hPL⟩ := hstep H hPH hconn
  have hHL : H ≤ L := by
    intro x y hxy
    exact (hadj x y).mpr (Or.inl hxy)
  have hLmem : L ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hKH.trans hHL, hPL⟩
  have hle : L.edgeSet.ncard ≤ H.edgeSet.ncard := hmax L hLmem
  have hLadj : L.Adj a b := (hadj a b).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  have hedge_in : s(a, b) ∈ L.edgeSet := (SimpleGraph.mem_edgeSet L).mpr hLadj
  have hedge_notin : s(a, b) ∉ H.edgeSet := by
    rw [SimpleGraph.mem_edgeSet]
    exact hnadj
  have hssub : H.edgeSet ⊂ L.edgeSet := by
    rw [Set.ssubset_iff_subset_ne]
    exact ⟨SimpleGraph.edgeSet_mono hHL, fun heq => hedge_notin (heq ▸ hedge_in)⟩
  have hlt : H.edgeSet.ncard < L.edgeSet.ncard :=
    Set.ncard_lt_ncard hssub (Set.toFinite L.edgeSet)
  omega
