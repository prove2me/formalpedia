-- Prove2me | solution 1 for WilliamsonShmoys.edge_bound_from_connected_induced_subgraphs__p2m_810fe5c7_ed69_412f_8871_a99b8e3c08fc_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:44:44.837022+00:00
-- url     : https://prove2.me/submissions/8228977a-d69b-411b-abae-4ef5ae926e8e

import Mathlib

namespace EbdHelp

open Classical

variable {V : Type} [Fintype V]

noncomputable def f (G : SimpleGraph V) (S : Finset V) : ℕ :=
  (G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ S)).card

lemma ncard_induce (G : SimpleGraph V) (S : Finset V) :
    (G.induce (S : Set V)).edgeSet.ncard = f G S := by
  have hinj : Function.Injective (Sym2.map (Subtype.val : ↥(S : Set V) → V)) :=
    by exact Sym2.map.injective Subtype.val_injective
  rw [← Set.ncard_image_of_injective _ hinj, f, ← Set.ncard_coe_finset]
  congr 1
  ext e
  constructor
  · rintro ⟨e', he', rfl⟩
    induction e' using Sym2.ind with
    | _ a b =>
      simp only [Sym2.map_mk, Finset.coe_filter, Set.mem_ofPred_eq,
        SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Sym2.mem_iff]
      refine ⟨by simpa using he', ?_⟩
      rintro v (rfl | rfl)
      · exact a.2
      · exact b.2
  · induction e using Sym2.ind with
    | _ x y =>
      simp only [Finset.coe_filter, Set.mem_ofPred_eq,
        SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Sym2.mem_iff]
      rintro ⟨h, hxy⟩
      have hx : x ∈ S := hxy x (Or.inl rfl)
      have hy : y ∈ S := hxy y (Or.inr rfl)
      exact ⟨s(⟨x, hx⟩, ⟨y, hy⟩), by simpa using h, by simp⟩

lemma f_le_choose (G : SimpleGraph V) (S : Finset V) : f G S ≤ S.card.choose 2 := by
  rw [← ncard_induce, ← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  have := (G.induce (S : Set V)).card_edgeFinset_le_card_choose_two
  simpa using this

lemma f_split (G : SimpleGraph V) (S A : Finset V) (hAS : A ⊆ S)
    (hno : ∀ a ∈ A, ∀ b ∈ S, b ∉ A → ¬ G.Adj a b) :
    f G S = f G A + f G (S \ A) := by
  unfold f
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext e
    induction e using Sym2.ind with
    | _ x y =>
      simp only [Finset.mem_filter, Finset.mem_union, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet, Sym2.mem_iff, forall_eq_or_imp, forall_eq, Finset.mem_sdiff]
      constructor
      · rintro ⟨h, hx, hy⟩
        by_cases hxA : x ∈ A <;> by_cases hyA : y ∈ A
        · exact Or.inl ⟨h, hxA, hyA⟩
        · exact absurd h (hno x hxA y hy hyA)
        · exact absurd h.symm (hno y hyA x hx hxA)
        · exact Or.inr ⟨h, ⟨hx, hxA⟩, ⟨hy, hyA⟩⟩
      · rintro (⟨h, hx, hy⟩ | ⟨h, ⟨hx, _⟩, ⟨hy, _⟩⟩)
        · exact ⟨h, hAS hx, hAS hy⟩
        · exact ⟨h, hx, hy⟩
  · rw [Finset.disjoint_left]
    intro e h1 h2
    induction e using Sym2.ind with
    | _ x y =>
      simp only [Finset.mem_filter, Sym2.mem_iff, forall_eq_or_imp, forall_eq,
        Finset.mem_sdiff] at h1 h2
      exact h2.2.1.2 h1.2.1

omit [Fintype V] in
lemma exists_split (G : SimpleGraph V) (S : Finset V) (hS : S.Nonempty)
    (hc : ¬ (G.induce (S : Set V)).Connected) :
    ∃ A ⊆ S, A.Nonempty ∧ (S \ A).Nonempty ∧
      ∀ a ∈ A, ∀ b ∈ S, b ∉ A → ¬ G.Adj a b := by
  rw [SimpleGraph.connected_iff] at hc
  have hne : Nonempty (S : Set V) := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  have hp : ¬ (G.induce (S : Set V)).Preconnected := fun h => hc ⟨h, hne⟩
  simp only [SimpleGraph.Preconnected, not_forall] at hp
  obtain ⟨u, w, huw⟩ := hp
  refine ⟨S.filter (fun x => ∃ hx : x ∈ S, (G.induce (S : Set V)).Reachable u ⟨x, hx⟩),
    Finset.filter_subset _ _, ⟨u.1, ?_⟩, ⟨w.1, ?_⟩, ?_⟩
  · simp only [Finset.mem_filter]
    exact ⟨u.2, u.2, SimpleGraph.Reachable.refl _⟩
  · simp only [Finset.mem_sdiff, Finset.mem_filter, not_and, not_exists]
    exact ⟨w.2, fun _ _ h => huw h⟩
  · intro a ha b hb hbA h
    simp only [Finset.mem_filter] at ha
    obtain ⟨_, haS, hr⟩ := ha
    apply hbA
    simp only [Finset.mem_filter]
    refine ⟨hb, hb, hr.trans ?_⟩
    exact SimpleGraph.Adj.reachable (by simpa using h)

lemma f_univ (G : SimpleGraph V) : f G Finset.univ = G.edgeSet.ncard := by
  rw [f, Finset.filter_true_of_mem (fun e _ v _ => Finset.mem_univ v),
    ← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]

lemma main (G : SimpleGraph V)
    (hLocal : ∀ S : Finset V, 3 <= S.card ->
      (G.induce (S : Set V)).Connected ->
      (G.induce (S : Set V)).edgeSet.ncard <= 3 * S.card - 6) :
    ∀ n, ∀ S : Finset V, S.card = n → 3 ≤ n → f G S + 6 ≤ 3 * n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hSn h3
    by_cases hc : (G.induce (S : Set V)).Connected
    · have := hLocal S (by omega) hc
      rw [ncard_induce] at this
      omega
    · have hS : S.Nonempty := by
        rw [← Finset.card_pos]; omega
      obtain ⟨A, hAS, hA, hB, hno⟩ := exists_split G S hS hc
      rw [f_split G S A hAS hno]
      have hcard : A.card + (S \ A).card = n := by
        rw [Finset.card_sdiff_of_subset hAS]
        have := Finset.card_le_card hAS
        omega
      have hA1 := hA.card_pos
      have hB1 := hB.card_pos
      have bound : ∀ T : Finset V, 0 < T.card → T.card < n →
          (3 ≤ T.card ∧ f G T + 6 ≤ 3 * T.card) ∨ (T.card = 1 ∧ f G T = 0) ∨
            (T.card = 2 ∧ f G T ≤ 1) := by
        intro T hT0 hTn
        by_cases h3 : 3 ≤ T.card
        · exact Or.inl ⟨h3, ih _ hTn T rfl h3⟩
        · have hc := f_le_choose G T
          interval_cases hT : T.card
          · right; left; simp at hc; exact ⟨rfl, hc⟩
          · right; right; simp at hc; exact ⟨rfl, hc⟩
      have bA := bound A hA1 (by omega)
      have bB := bound (S \ A) hB1 (by omega)
      omega

end EbdHelp

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hLocal : ∀ S : Finset V, 3 <= S.card ->
      (G.induce (S : Set V)).Connected ->
      (G.induce (S : Set V)).edgeSet.ncard <= 3 * S.card - 6) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  have h := EbdHelp.main G hLocal _ Finset.univ rfl (by simpa using hV)
  have he : G.edgeSet.ncard = EbdHelp.f G Finset.univ := (EbdHelp.f_univ G).symm
  rw [he]
  simp only [Finset.card_univ] at h
  omega
