-- Prove2me | solution 1 for WilliamsonShmoys.iterate_planar_bridges__p2m_ecabda78_d401_4f6a_900f_746421d84865_a2
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-11T15:15:41.927825+00:00
-- url     : https://prove2.me/submissions/b08d3a3e-00e7-443d-97e2-622b04e2687c

import Mathlib

set_option autoImplicit false

/-- Repeatedly adjoining edges between unreachable vertices eventually yields a connected graph. -/
theorem solution {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : P K)
    (hStep : ∀ (G : SimpleGraph V), P G → 3 ≤ Fintype.card V → ¬ G.Connected →
      ∃ u v : V,
        u ≠ v ∧ ¬ G.Reachable u v ∧ ¬ G.Adj u v ∧
        P (G ⊔ SimpleGraph.fromRel (fun x y : V => x = u ∧ y = v)))
    (hDisconnected : ¬ K.Connected) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ H.Connected ∧ P H := by
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
  obtain ⟨u, v, hne, hnreach, hnadj, hP'⟩ := hStep H hPH hV hconn
  let L : SimpleGraph V := H ⊔ SimpleGraph.fromRel (fun x y : V => x = u ∧ y = v)
  have hHL : H ≤ L := le_sup_left
  have hLmem : L ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hKH.trans hHL, hP'⟩
  have hle : L.edgeSet.ncard ≤ H.edgeSet.ncard := hmax L hLmem
  have hedge_in : s(u, v) ∈ L.edgeSet := by
    change s(u, v) ∈ (H ⊔ SimpleGraph.fromRel (fun x y : V => x = u ∧ y = v)).edgeSet
    rw [SimpleGraph.mem_edgeSet, SimpleGraph.sup_adj]
    right
    rw [SimpleGraph.fromRel_adj]
    exact ⟨hne, Or.inl ⟨rfl, rfl⟩⟩
  have hedge_notin : s(u, v) ∉ H.edgeSet := by
    rw [SimpleGraph.mem_edgeSet]
    exact hnadj
  have hssub : H.edgeSet ⊂ L.edgeSet := by
    rw [Set.ssubset_iff_subset_ne]
    exact ⟨SimpleGraph.edgeSet_mono hHL, fun heq => hedge_notin (heq ▸ hedge_in)⟩
  have hlt : H.edgeSet.ncard < L.edgeSet.ncard :=
    Set.ncard_lt_ncard hssub (Set.toFinite L.edgeSet)
  omega
