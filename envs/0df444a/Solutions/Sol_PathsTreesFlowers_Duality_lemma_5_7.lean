-- Prove2me | solution 1 for PathsTreesFlowers.Duality.lemma_5_7
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T08:11:58.016358+00:00
-- url     : https://prove2.me/submissions/15158c4e-06d4-4a93-aba2-81ba30334a3c

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Duality_Basic
import Definitions.Def_PathsTreesFlowers_Duality_OddSetCover



namespace PathsTreesFlowers.Duality

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

lemma ptf_card_ends (G : EdmondsMatching65.Polyhedron.Graph V E) (U : Finset V) (e : E)
    (h : G.ends e ∈ U.sym2) : (U.filter (fun v => v ∈ G.ends e)).card = 2 := by
  have hl := G.loopless e
  generalize G.ends e = z at h hl
  induction z using Sym2.ind with
  | h a b =>
    rw [Finset.mk_mem_sym2_iff] at h
    rw [Sym2.mk_isDiag_iff] at hl
    have : U.filter (fun v => v ∈ s(a, b)) = {a, b} := by
      ext v; simp only [Finset.mem_filter, Sym2.mem_iff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨_, h'⟩; exact h'
      · rintro (rfl | rfl)
        · exact ⟨h.1, Or.inl rfl⟩
        · exact ⟨h.2, Or.inr rfl⟩
    rw [this, Finset.card_pair hl]

lemma ptf_univ_card (G : EdmondsMatching65.Polyhedron.Graph V E) (M : Finset E)
    (hM : EdmondsMatching65.Polyhedron.IsMatching G M) :
    Fintype.card V = 2 * M.card + (Finset.univ.filter (IsExposed G M)).card := by
  have hdisj : ∀ e ∈ M, ∀ f ∈ M, e ≠ f →
      Disjoint (Finset.univ.filter (fun v => v ∈ G.ends e))
        (Finset.univ.filter (fun v => v ∈ G.ends f)) := by
    intro e he f hf hne
    rw [Finset.disjoint_left]
    intro v hv hv'
    simp only [Finset.mem_filter] at hv hv'
    exact hM e he f hf hne v hv.2 hv'.2
  have hc : (M.biUnion (fun e => Finset.univ.filter (fun v => v ∈ G.ends e))).card
      = 2 * M.card := by
    rw [Finset.card_biUnion (fun e he f hf hne => hdisj e he f hf hne)]
    rw [Finset.sum_congr rfl (fun e _ => ptf_card_ends G Finset.univ e
      (by rw [Finset.mem_sym2_iff]; intro a _; exact Finset.mem_univ a))]
    simp [mul_comm]
  have hsplit : (M.biUnion (fun e => Finset.univ.filter (fun v => v ∈ G.ends e))) =
      Finset.univ.filter (fun v => ¬ IsExposed G M v) := by
    ext v
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold IsExposed
    constructor
    · rintro ⟨e, he, hv⟩ h; exact h e he hv
    · intro h; by_contra h'; apply h; intro e he hv; exact h' ⟨e, he, hv⟩
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V)) (IsExposed G M)
  rw [Finset.card_univ] at this
  rw [← hc, hsplit]; omega

theorem l57_core (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (hM : EdmondsMatching65.Polyhedron.IsMatching G M)
    (hexp : (Finset.univ.filter (IsExposed G M)).card ≤ 1) :
    ∃ S : Finset (Finset V), IsOddSetCover G S ∧ capacitySum S = M.card := by
  have hn := ptf_univ_card G M hM
  set x := (Finset.univ.filter (IsExposed G M)).card with hx
  have hedge : ∀ e : E, 2 ≤ Fintype.card V := by
    intro e
    have := ptf_card_ends G Finset.univ e
      (by rw [Finset.mem_sym2_iff]; intro a _; exact Finset.mem_univ a)
    have h2 := Finset.card_le_univ (Finset.univ.filter (fun v => v ∈ G.ends e))
    omega
  by_cases hm : M.card = 0
  · refine ⟨∅, ⟨by simp, ?_⟩, by simp [capacitySum, hm]⟩
    intro e; have := hedge e; omega
  have hm1 : 1 ≤ M.card := Nat.pos_of_ne_zero hm
  have hmem : ∀ (U : Finset V) (e : E), (∀ v ∈ G.ends e, v ∈ U) → G.ends e ∈ U.sym2 := by
    intro U e h; rw [Finset.mem_sym2_iff]; exact h
  by_cases hx1 : x = 1
  · refine ⟨{Finset.univ}, ⟨?_, ?_⟩, ?_⟩
    · intro U hU; rw [Finset.mem_singleton] at hU; subst hU
      unfold IsOddSet; rw [Finset.card_univ]; exact ⟨M.card, by omega⟩
    · intro e
      refine ⟨Finset.univ, Finset.mem_singleton_self _, ?_⟩
      have h3 : (Finset.univ : Finset V).card ≠ 1 := by rw [Finset.card_univ]; omega
      unfold Covers; rw [if_neg h3]
      exact hmem _ e (fun v _ => Finset.mem_univ v)
    · rw [capacitySum, Finset.sum_singleton, capacity, Finset.card_univ]
      have : Fintype.card V ≠ 1 := by omega
      rw [if_neg this]; omega
  · have hx0 : x = 0 := by omega
    by_cases hm2 : M.card = 1
    · have hV : Fintype.card V = 2 := by omega
      obtain ⟨a⟩ : Nonempty V := Fintype.card_pos_iff.1 (by omega)
      refine ⟨{{a}}, ⟨?_, ?_⟩, ?_⟩
      · intro U hU; rw [Finset.mem_singleton] at hU; subst hU
        unfold IsOddSet; simp
      · intro e
        refine ⟨{a}, Finset.mem_singleton_self _, ?_⟩
        unfold Covers; rw [if_pos (Finset.card_singleton a)]
        refine ⟨a, Finset.mem_singleton_self _, ?_⟩
        have h2 := ptf_card_ends G Finset.univ e
          (by rw [Finset.mem_sym2_iff]; intro a _; exact Finset.mem_univ a)
        have h3 : Finset.univ.filter (fun v => v ∈ G.ends e) = Finset.univ :=
          Finset.eq_univ_of_card _ (by rw [h2, hV])
        have : a ∈ Finset.univ.filter (fun v => v ∈ G.ends e) := by rw [h3]; exact Finset.mem_univ a
        exact (Finset.mem_filter.1 this).2
      · simp [capacitySum, capacity, hm2]
    · obtain ⟨v⟩ : Nonempty V := Fintype.card_pos_iff.1 (by omega)
      have hne : (Finset.univ.erase v) ≠ {v} := by
        intro h
        have := congrArg Finset.card h
        rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ,
          Finset.card_singleton] at this
        omega
      refine ⟨{Finset.univ.erase v, {v}}, ⟨?_, ?_⟩, ?_⟩
      · intro U hU
        rw [Finset.mem_insert, Finset.mem_singleton] at hU
        rcases hU with rfl | rfl
        · unfold IsOddSet
          rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]
          exact ⟨M.card - 1, by omega⟩
        · unfold IsOddSet; simp
      · intro e
        by_cases hv : v ∈ G.ends e
        · refine ⟨{v}, by simp, ?_⟩
          unfold Covers; rw [if_pos (Finset.card_singleton v)]
          exact ⟨v, Finset.mem_singleton_self _, hv⟩
        · refine ⟨Finset.univ.erase v, by simp, ?_⟩
          have h3 : (Finset.univ.erase v).card ≠ 1 := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]; omega
          unfold Covers; rw [if_neg h3]
          exact hmem _ e (fun w hw => Finset.mem_erase.2 ⟨fun h => hv (h ▸ hw), Finset.mem_univ w⟩)
      · rw [capacitySum, Finset.sum_pair hne, capacity, capacity,
          Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Finset.card_singleton]
        have : Fintype.card V - 1 ≠ 1 := by omega
        rw [if_neg this]; simp; omega

end PathsTreesFlowers.Duality

open PathsTreesFlowers.Duality


theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (hM : EdmondsMatching65.Polyhedron.IsMatching G M)
    (hexp : (Finset.univ.filter (IsExposed G M)).card ≤ 1) :
    ∃ S : Finset (Finset V), IsOddSetCover G S ∧ capacitySum S = M.card := by
  exact l57_core G M hM hexp
