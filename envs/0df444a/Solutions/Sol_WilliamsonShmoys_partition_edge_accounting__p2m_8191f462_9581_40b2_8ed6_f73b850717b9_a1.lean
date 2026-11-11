-- Prove2me | solution 1 for WilliamsonShmoys.partition_edge_accounting__p2m_8191f462_9581_40b2_8ed6_f73b850717b9_a1
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-10T16:53:08.97568+00:00
-- url     : https://prove2.me/submissions/a0d2ce6c-f3fe-4cb9-87c3-eaf9574fc60d

import Mathlib

open scoped BigOperators

/-- If the vertex set is split into pairwise disjoint blocks and every edge has both endpoints in
one block, then the edges of `L` are counted by summing the edges of the subgraphs induced on the
blocks. -/
theorem solution {V : Type*} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (C : V → Finset V)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hcover : Finset.univ.biUnion C = Finset.univ)
    (hlocal : ∀ u v, L.Adj u v → ∃ i, u ∈ C i ∧ v ∈ C i) :
    L.edgeSet.ncard = ∑ i : V, (L.induce (fun v => v ∈ C i)).edgeSet.ncard := by
  classical
  haveI : Fintype ↑L.edgeSet := Set.Finite.fintype (Set.toFinite L.edgeSet)
  have key : ∀ s : Finset V,
      (L.induce (fun v => v ∈ s)).edgeSet.ncard = (L.edgeFinset ∩ s.sym2).card := by
    intro s
    have hmap : (L.induce (fun v => v ∈ s)).edgeFinset.map
        (Function.Embedding.subtype (fun v => v ∈ s)).sym2Map = L.edgeFinset ∩ s.sym2 := by
      ext e
      constructor
      · intro he
        rw [Finset.mem_map] at he
        obtain ⟨a, ha, rfl⟩ := he
        induction a using Sym2.ind with
        | _ u v =>
          have h2 : s(u, v) ∈ (L.induce (fun v => v ∈ s)).edgeSet := by
            simpa [SimpleGraph.edgeFinset] using ha
          have hadj : L.Adj u.val v.val := (SimpleGraph.mem_edgeSet _).mp h2
          rw [Finset.mem_inter, Finset.mem_sym2_iff]
          refine ⟨?_, ?_⟩
          · simp only [SimpleGraph.mem_edgeFinset]
            exact hadj
          · intro x hx
            rcases Sym2.mem_iff.mp hx with h | h
            · rw [h]; exact u.property
            · rw [h]; exact v.property
      · intro he
        rw [Finset.mem_inter, Finset.mem_sym2_iff] at he
        obtain ⟨he, hsub⟩ := he
        rw [Finset.mem_map]
        induction e using Sym2.ind with
        | _ x y =>
          have hadj : L.Adj x y := by
            have h2 : s(x, y) ∈ L.edgeSet := by
              simpa [SimpleGraph.edgeFinset] using he
            exact (SimpleGraph.mem_edgeSet L).mp h2
          have hx : x ∈ s := hsub x (Sym2.mem_mk_left x y)
          have hy : y ∈ s := hsub y (Sym2.mem_mk_right x y)
          refine ⟨s(⟨x, hx⟩, ⟨y, hy⟩), ?_, ?_⟩
          · simp only [SimpleGraph.mem_edgeFinset]
            exact hadj
          · rfl
    rw [Set.ncard_eq_toFinset_card']
    change (L.induce (fun v => v ∈ s)).edgeFinset.card = (L.edgeFinset ∩ s.sym2).card
    rw [← Finset.card_map (f := (Function.Embedding.subtype (fun v => v ∈ s)).sym2Map), hmap]
  set B : V → Finset (Sym2 V) := fun i => L.edgeFinset ∩ (C i).sym2 with hB
  have hterm : ∀ i : V, (L.induce (fun v => v ∈ C i)).edgeSet.ncard = (B i).card := by
    intro i
    simpa only [hB] using key (C i)
  have hnonempty : ∀ e : Sym2 V, e.toFinset.Nonempty := by
    intro e
    induction e using Sym2.ind with
    | _ u v => exact ⟨u, by simp⟩
  have hmem : ∀ e ∈ L.edgeFinset, e ∈ Finset.univ.biUnion B := by
    intro e he
    revert he
    induction e using Sym2.ind with
    | _ u v =>
      intro he
      have h1 : s(u, v) ∈ L.edgeSet := by simpa [SimpleGraph.edgeFinset] using he
      have hadj : L.Adj u v := (SimpleGraph.mem_edgeSet L).mp h1
      obtain ⟨i, hu, hv⟩ := hlocal u v hadj
      refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ?_⟩
      simp only [hB, Finset.mem_inter]
      refine ⟨he, ?_⟩
      rw [Finset.mem_sym2_iff]
      intro a ha
      rcases Sym2.mem_iff.mp ha with h | h
      · rw [h]; exact hu
      · rw [h]; exact hv
  have hcoverB : Finset.univ.biUnion B = L.edgeFinset := by
    ext e
    refine ⟨?_, hmem e⟩
    intro he
    rw [Finset.mem_biUnion] at he
    obtain ⟨i, _, hi⟩ := he
    exact (Finset.mem_inter.mp hi).1
  have hdisj : ((Finset.univ : Finset V) : Set V).PairwiseDisjoint B := by
    intro i _ j _ hij
    change Disjoint (B i) (B j)
    rw [Finset.disjoint_left]
    intro e he he'
    simp only [hB, Finset.mem_inter] at he he'
    rw [Finset.mem_sym2_iff] at he he'
    obtain ⟨a, ha⟩ := hnonempty e
    have ha' : a ∈ e := by rwa [Sym2.mem_toFinset] at ha
    have hai : a ∈ C i := he.2 a ha'
    have haj : a ∈ C j := he'.2 a ha'
    exact (Finset.disjoint_left.mp (hdisjoint i j hij) hai) haj
  have hcard : L.edgeFinset.card = ∑ i : V, (B i).card := by
    rw [← hcoverB, Finset.card_biUnion hdisj]
  calc L.edgeSet.ncard = L.edgeFinset.card := by
        rw [Set.ncard_eq_toFinset_card']
        rfl
    _ = ∑ i : V, (B i).card := hcard
    _ = ∑ i : V, (L.induce (fun v => v ∈ C i)).edgeSet.ncard :=
        Finset.sum_congr rfl (fun i _ => (hterm i).symm)
