-- Prove2me | solution 1 for PathsTreesFlowers.Duality.weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T08:10:28.605104+00:00
-- url     : https://prove2.me/submissions/78a595da-4fc6-44f1-b104-6013ecd36f12

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
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

lemma ptf_cover_le (G : EdmondsMatching65.Polyhedron.Graph V E) (M : Finset E)
    (hM : EdmondsMatching65.Polyhedron.IsMatching G M) (U : Finset V) (hU : IsOddSet U) :
    (M.filter (Covers G U)).card ≤ capacity U := by
  unfold capacity
  by_cases h1 : U.card = 1
  · rw [if_pos h1]
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.1 h1
    rw [Finset.card_le_one]
    intro e he f hf
    simp only [Finset.mem_filter, Covers, Finset.card_singleton, if_true, Finset.mem_singleton] at he hf
    obtain ⟨he, w, hw0, hw⟩ := he
    obtain ⟨hf, w', hw0', hw'⟩ := hf
    by_contra hne
    exact hM e he f hf hne w hw (hw0.trans hw0'.symm ▸ hw')
  · rw [if_neg h1]
    set F := M.filter (Covers G U) with hF
    have hin : ∀ e ∈ F, G.ends e ∈ U.sym2 := by
      intro e he
      simp only [hF, Finset.mem_filter, Covers, if_neg h1] at he
      exact he.2
    have hdisj : ∀ e ∈ F, ∀ f ∈ F, e ≠ f →
        Disjoint (U.filter (fun v => v ∈ G.ends e)) (U.filter (fun v => v ∈ G.ends f)) := by
      intro e he f hf hne
      rw [Finset.disjoint_left]
      intro v hv hv'
      simp only [Finset.mem_filter] at hv hv'
      exact hM e (Finset.mem_filter.1 he).1 f (Finset.mem_filter.1 hf).1 hne v hv.2 hv'.2
    have hc : (F.biUnion (fun e => U.filter (fun v => v ∈ G.ends e))).card = 2 * F.card := by
      rw [Finset.card_biUnion (fun e he f hf hne => hdisj e he f hf hne)]
      rw [Finset.sum_congr rfl (fun e he => ptf_card_ends G U e (hin e he))]
      simp [mul_comm]
    have hsub : (F.biUnion (fun e => U.filter (fun v => v ∈ G.ends e))) ⊆ U := by
      intro v hv
      simp only [Finset.mem_biUnion, Finset.mem_filter] at hv
      obtain ⟨_, _, hv, _⟩ := hv; exact hv
    have := Finset.card_le_card hsub
    obtain ⟨k, hk⟩ := hU
    omega

theorem wd_core (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (S : Finset (Finset V))
    (hM : EdmondsMatching65.Polyhedron.IsMatching G M) (hS : IsOddSetCover G S) :
    M.card ≤ capacitySum S := by
  classical
  choose! f hfS hfc using hS.2
  have h1 : M.card = ∑ U ∈ S, (M.filter (fun e => f e = U)).card :=
    Finset.card_eq_sum_card_fiberwise (fun e he => hfS e)
  rw [h1, capacitySum]
  apply Finset.sum_le_sum
  intro U hU
  refine le_trans (Finset.card_le_card ?_) (ptf_cover_le G M hM U (hS.1 U hU))
  intro e he
  simp only [Finset.mem_filter] at he ⊢
  exact ⟨he.1, he.2 ▸ hfc e⟩

end PathsTreesFlowers.Duality

open PathsTreesFlowers.Duality


theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (S : Finset (Finset V))
    (hM : EdmondsMatching65.Polyhedron.IsMatching G M) (hS : IsOddSetCover G S) :
    M.card ≤ capacitySum S := by
  exact wd_core G M S hM hS
