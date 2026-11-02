-- Prove2me | solution 1 for WilliamsonShmoys.finite_component_partition_core__p2m_43810500_1f43_4f26_9fb2_357a895d104d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T21:15:33.621797+00:00
-- url     : https://prove2.me/submissions/522856f1-bcc4-4db1-81ff-3136b5df0ee8

import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
     ∃ C : Finset (Finset V),
      (∀ B ∈ C, 0 < B.card) ∧
      (∀ B₁ ∈ C, ∀ B₂ ∈ C, B₁ ≠ B₂ →
        Disjoint (↑B₁ : Set V) (↑B₂ : Set V)) ∧
      (∀ v : V, ∃ B ∈ C, v ∈ B) ∧
      Fintype.card V = ∑ B ∈ C, B.card ∧
      (∀ B ∈ C,
        letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _
        (N.induce (↑B : Set V)).Connected) ∧
      (∀ B ∈ C, B.card = 1 →
        letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _
        (N.induce (↑B : Set V)).edgeFinset.card = 0) ∧
      (∀ B ∈ C, B.card = 2 →
        letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _
        (N.induce (↑B : Set V)).edgeFinset.card ≤ 1)) := by
  classical
  letI : DecidableRel N.Adj := Classical.decRel N.Adj
  let f : N.ConnectedComponent → Finset V := fun c => c.supp.toFinset
  let C : Finset (Finset V) := Finset.univ.image f
  have hf : Function.Injective f := by
    intro c d h
    apply SimpleGraph.ConnectedComponent.supp_injective
    simpa [f] using congrArg (fun s : Finset V => (s : Set V)) h
  refine ⟨C, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro B hB
    rcases Finset.mem_image.mp hB with ⟨c, -, rfl⟩
    rcases c.nonempty_supp with ⟨v, hv⟩
    apply Finset.card_pos.mpr
    exact ⟨v, by simpa [f] using hv⟩
  · intro B₁ hB₁ B₂ hB₂ hne
    rcases Finset.mem_image.mp hB₁ with ⟨c₁, -, rfl⟩
    rcases Finset.mem_image.mp hB₂ with ⟨c₂, -, rfl⟩
    have hcd : c₁ ≠ c₂ := fun h => hne (congrArg f h)
    simpa [f] using SimpleGraph.pairwise_disjoint_supp_connectedComponent N hcd
  · intro v
    refine ⟨f (N.connectedComponentMk v), Finset.mem_image.mpr
      ⟨N.connectedComponentMk v, Finset.mem_univ _, rfl⟩, ?_⟩
    simpa [f] using
      (SimpleGraph.ConnectedComponent.connectedComponentMk_mem (G := N) v)
  · calc
      Fintype.card V = Fintype.card (Σ c : N.ConnectedComponent, c.supp) := by
        apply Fintype.card_congr
        refine Equiv.mk ?_ ?_ ?_ ?_
        · intro v
          exact ⟨N.connectedComponentMk v,
            ⟨v, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩⟩
        · intro x
          exact x.2.1
        · intro v
          rfl
        · rintro ⟨c, ⟨v, hv⟩⟩
          have hc : N.connectedComponentMk v = c :=
            (SimpleGraph.ConnectedComponent.mem_supp_iff c v).mp hv
          subst c
          rfl
      _ = ∑ c : N.ConnectedComponent, Fintype.card c.supp := Fintype.card_sigma
      _ = ∑ c : N.ConnectedComponent, (c.supp.toFinset).card := by simp
      _ = ∑ B ∈ C, B.card := by
        symm
        change (∑ B ∈ Finset.univ.image f, B.card) =
          ∑ c ∈ Finset.univ, (f c).card
        rw [Finset.sum_image]
        intro c hc d hd hcd
        exact hf hcd
  · intro B hB
    rcases Finset.mem_image.mp hB with ⟨c, -, hB⟩
    subst B
    have hs : ((f c : Finset V) : Set V) = c.supp := by
      ext v
      simp [f]
    rw [hs]
    exact c.connected_toSimpleGraph
  · constructor
    · intro B hB hsize
      rcases Finset.mem_image.mp hB with ⟨c, -, hB⟩
      subst B
      letI : Fintype {v // v ∈ (↑(f c) : Set V)} := Fintype.ofFinite _
      have hcard : Fintype.card {v // v ∈ (↑(f c) : Set V)} = (f c).card := by simp
      have hbound := (N.induce (↑(f c) : Set V)).card_edgeFinset_le_card_choose_two
      have hle : (N.induce (↑(f c) : Set V)).edgeFinset.card ≤ 0 := by
        simpa [hcard, hsize] using hbound
      exact Nat.eq_zero_of_le_zero hle
    · intro B hB hsize
      rcases Finset.mem_image.mp hB with ⟨c, -, hB⟩
      subst B
      letI : Fintype {v // v ∈ (↑(f c) : Set V)} := Fintype.ofFinite _
      have hcard : Fintype.card {v // v ∈ (↑(f c) : Set V)} = (f c).card := by simp
      have hbound := (N.induce (↑(f c) : Set V)).card_edgeFinset_le_card_choose_two
      rw [hcard, hsize] at hbound
      norm_num at hbound
      exact hbound
