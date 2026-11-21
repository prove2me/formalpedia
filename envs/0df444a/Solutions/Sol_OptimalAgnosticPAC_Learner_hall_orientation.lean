-- Prove2me | solution 1 for OptimalAgnosticPAC.Learner.hall_orientation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:02:42.276139+00:00
-- url     : https://prove2.me/submissions/1344c473-2150-4258-8173-d242a903e344

import Mathlib
import Definitions.Def_OptimalAgnosticPAC_Learner_Cube

section
open scoped Classical
namespace OptimalAgnosticPAC.Dev.Hall
open OptimalAgnosticPAC.Learner

theorem assign {V : Type*} [Fintype V] (G : SimpleGraph V) (c : V → ℕ)
    (hc : ∀ W : Finset V, (inducedEdges G W).card ≤ ∑ x ∈ W, c x) :
    ∃ f : G.edgeFinset → (Σ x : V, Fin (c x)), Function.Injective f ∧
      ∀ e, (f e).1 ∈ e.1 := by
  let t : G.edgeFinset → Finset (Σ x : V, Fin (c x)) :=
    fun e => Finset.univ.filter (fun s => s.1 ∈ e.1)
  have key : ∀ s : Finset G.edgeFinset, s.card ≤ (s.biUnion t).card := by
    intro s
    let W : Finset V := Finset.univ.filter (fun x => ∃ e ∈ s, x ∈ e.1)
    have h1 : s.card ≤ (inducedEdges G W).card := by
      have : (s.map (Function.Embedding.subtype _)) ⊆ inducedEdges G W := by
        intro e he
        simp only [Finset.mem_map, Function.Embedding.coe_subtype] at he
        obtain ⟨e', he', rfl⟩ := he
        simp only [inducedEdges, Finset.mem_filter]
        refine ⟨e'.2, fun x hx => ?_⟩
        simp only [W, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨e', he', hx⟩
      simpa using Finset.card_le_card this
    have h2 : s.biUnion t = W.sigma (fun x => (Finset.univ : Finset (Fin (c x)))) := by
      ext ⟨x, j⟩
      simp [t, W]
    rw [h2, Finset.card_sigma]
    simpa using h1.trans (hc W)
  obtain ⟨f, hf, hmem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 key
  exact ⟨f, hf, fun e => by simpa [t] using hmem e⟩

theorem main {V : Type*} [Fintype V] (G : SimpleGraph V) (c : V → ℕ)
    (hc : ∀ W : Finset V, (inducedEdges G W).card ≤ ∑ x ∈ W, c x) :
    (∃ a : Sym2 V → V, (∀ e ∈ G.edgeSet, a e ∈ e) ∧
      ∀ x, (G.edgeFinset.filter (fun e => a e = x)).card ≤ c x) ∧
    (∃ σ : Sym2 V → V, IsOrientation G σ ∧ ∀ x, outdegree G σ x ≤ c x) := by
  obtain ⟨f, hf, hmem⟩ := assign G c hc
  let a : Sym2 V → V := fun e =>
    if h : e ∈ G.edgeFinset then (f ⟨e, h⟩).1 else (Quot.out e).1
  have ha : ∀ (e : G.edgeFinset), a e.1 = (f e).1 := by
    intro e; simp only [a, dif_pos e.2]
  have hcount : ∀ x, (G.edgeFinset.filter (fun e => a e = x)).card ≤ c x := by
    intro x
    have h1 : G.edgeFinset.filter (fun e => a e = x) =
        (Finset.univ.filter (fun e : G.edgeFinset => (f e).1 = x)).map
          (Function.Embedding.subtype _) := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and,
        Function.Embedding.coe_subtype]
      constructor
      · rintro ⟨he, hx⟩
        exact ⟨⟨e, he⟩, by rw [← ha ⟨e, he⟩]; exact hx, rfl⟩
      · rintro ⟨e', hx, rfl⟩
        exact ⟨e'.2, by rw [ha]; exact hx⟩
    have h2 : (Finset.univ.filter (fun e : G.edgeFinset => (f e).1 = x)).card ≤
        (Finset.univ.filter (fun s : (Σ y : V, Fin (c y)) => s.1 = x)).card :=
      Finset.card_le_card_of_injOn f (fun e he => by simpa using he) (hf.injOn)
    have h3 : (Finset.univ.filter (fun s : (Σ y : V, Fin (c y)) => s.1 = x)).card = c x := by
      have : (Finset.univ.filter (fun s : (Σ y : V, Fin (c y)) => s.1 = x)) =
          ({x} : Finset V).sigma (fun y => (Finset.univ : Finset (Fin (c y)))) := by
        ext ⟨y, j⟩; simp
      rw [this, Finset.card_sigma]; simp
    rw [h1, Finset.card_map]; omega
  have hmemE : ∀ e ∈ G.edgeSet, a e ∈ e := by
    intro e he
    have := hmem ⟨e, by simpa using he⟩
    rw [ha ⟨e, by simpa using he⟩]; exact this
  refine ⟨⟨a, hmemE, hcount⟩, ?_⟩
  let σ : Sym2 V → V := fun e =>
    if h : e ∈ G.edgeSet then Sym2.Mem.other' (hmemE e h) else (Quot.out e).1
  have hσ : ∀ e (h : e ∈ G.edgeSet), σ e = Sym2.Mem.other' (hmemE e h) := by
    intro e h; simp only [σ, dif_pos h]
  refine ⟨σ, fun e he => ?_, fun x => ?_⟩
  · rw [hσ e he]; exact Sym2.other_mem' _
  · refine le_trans (Finset.card_le_card ?_) (hcount x)
    intro e he
    simp only [Finset.mem_filter] at he ⊢
    obtain ⟨heE, hxe, hne⟩ := he
    refine ⟨heE, ?_⟩
    have heE' : e ∈ G.edgeSet := by simpa using heE
    rw [hσ e heE'] at hne
    have hspec := Sym2.other_spec' (hmemE e heE')
    rw [← hspec] at hxe
    rw [Sym2.mem_iff] at hxe
    rcases hxe with h | h
    · exact h.symm
    · exact absurd h.symm hne
end OptimalAgnosticPAC.Dev.Hall

namespace OptimalAgnosticPAC.Learner
open scoped Classical

theorem chk_hall_orientation {V : Type*} [Fintype V] (G : SimpleGraph V) (c : V → ℕ)
    (hc : ∀ W : Finset V, (inducedEdges G W).card ≤ ∑ x ∈ W, c x) :
    (∃ a : Sym2 V → V, (∀ e ∈ G.edgeSet, a e ∈ e) ∧
      ∀ x, (G.edgeFinset.filter (fun e => a e = x)).card ≤ c x) ∧
    (∃ σ : Sym2 V → V, IsOrientation G σ ∧ ∀ x, outdegree G σ x ≤ c x) :=
  OptimalAgnosticPAC.Dev.Hall.main G c hc
end OptimalAgnosticPAC.Learner
end

theorem solution : type_of% @OptimalAgnosticPAC.Learner.chk_hall_orientation := @OptimalAgnosticPAC.Learner.chk_hall_orientation
