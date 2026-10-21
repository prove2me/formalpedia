-- Prove2me | solution 1 for TuranMatching.ColorCritical.card_highDeg_le
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:43:55.491531+00:00
-- url     : https://prove2.me/submissions/7849104a-d9b7-4b93-b683-24c90f71cb99

import Mathlib
import Definitions.Def_TuranMatching_ColorCritical_Setting

set_option autoImplicit false
open Finset SimpleGraph

namespace TMCAux

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma card_le_matchingNumber (G : SimpleGraph V) (E : Finset (Sym2 V))
    (hE : ∀ e ∈ E, e ∈ G.edgeSet)
    (hd : ∀ e ∈ E, ∀ e' ∈ E, ∀ v, v ∈ e → v ∈ e' → e = e') :
    E.card ≤ TuranMatching.Clique.matchingNumber G := by
  let M : G.Subgraph :=
    { verts := {v | ∃ e ∈ E, v ∈ e}
      Adj := fun a b => s(a, b) ∈ E
      adj_sub := fun {a b} h => hE _ h
      edge_vert := fun {a b} h => ⟨_, h, Sym2.mem_mk_left a b⟩
      symm := ⟨fun a b (h : s(a, b) ∈ E) => by rwa [Sym2.eq_swap]⟩ }
  have hM : M.IsMatching := by
    intro v hv
    obtain ⟨e, he, hve⟩ := hv
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hve
    refine ⟨w, he, fun w' (hw' : s(v, w') ∈ E) => ?_⟩
    exact Sym2.congr_right.mp (hd _ hw' _ he v (Sym2.mem_mk_left _ _) (Sym2.mem_mk_left _ _))
  have hedge : M.edgeSet = (↑E : Set (Sym2 V)) := by
    ext e
    induction e using Sym2.ind with
    | h a b => exact Iff.rfl
  have hbdd : BddAbove {m | ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = m} := by
    refine ⟨(Set.univ : Set (Sym2 V)).ncard, ?_⟩
    rintro m ⟨M', -, rfl⟩
    exact Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
  calc E.card = (↑E : Set (Sym2 V)).ncard := (Set.ncard_coe_finset E).symm
    _ = M.edgeSet.ncard := by rw [hedge]
    _ ≤ _ := le_csSup hbdd ⟨M, hM, rfl⟩

lemma greedy (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) (X B : Finset V)
    (hdeg : ∀ a ∈ X, 2 * s < G.degree a) (hcard : 2 * X.card + B.card ≤ 2 * s + 2) :
    ∃ p : V → V, (∀ a ∈ X, G.Adj a (p a)) ∧ (∀ a ∈ X, p a ∉ X) ∧ (∀ a ∈ X, p a ∉ B) ∧
      Set.InjOn p X := by
  have key : ∀ Y : Finset V, Y ⊆ X → ∃ p : V → V, (∀ a ∈ Y, G.Adj a (p a)) ∧
      (∀ a ∈ Y, p a ∉ X) ∧ (∀ a ∈ Y, p a ∉ B) ∧ Set.InjOn p Y := by
    intro Y
    induction Y using Finset.induction_on with
    | empty => intro _; exact ⟨id, by simp, by simp, by simp, by simp⟩
    | insert a Y ha ih =>
      intro hsub
      obtain ⟨p, h1, h2, h3, h4⟩ := ih (fun x hx => hsub (Finset.mem_insert_of_mem hx))
      have haX : a ∈ X := hsub (Finset.mem_insert_self a Y)
      have hYX : Y.card < X.card :=
        Finset.card_lt_card ⟨fun x hx => hsub (Finset.mem_insert_of_mem hx), fun h => ha (h haX)⟩
      have hFc : (X ∪ B ∪ Y.image p).card ≤ X.card + B.card + Y.card :=
        (Finset.card_union_le _ _).trans
          (Nat.add_le_add (Finset.card_union_le _ _) Finset.card_image_le)
      obtain ⟨b, hb, hbF⟩ : ∃ b ∈ G.neighborFinset a, b ∉ X ∪ B ∪ Y.image p := by
        by_contra hcon
        push_neg at hcon
        have hsub2 : G.neighborFinset a ⊆ (X ∪ B ∪ Y.image p).erase a := by
          intro b hb
          refine Finset.mem_erase.mpr ⟨?_, hcon b hb⟩
          rintro rfl
          simp at hb
        have := Finset.card_le_card hsub2
        rw [Finset.card_erase_of_mem (by simp [haX])] at this
        have hd := hdeg a haX
        rw [← SimpleGraph.card_neighborFinset_eq_degree] at hd
        omega
      have hbadj : G.Adj a b := by simpa using hb
      simp only [Finset.mem_union, Finset.mem_image, not_or, not_exists, not_and] at hbF
      obtain ⟨⟨hbX, hbB⟩, hbY⟩ := hbF
      refine ⟨Function.update p a b, ?_, ?_, ?_, ?_⟩
      · intro x hx
        by_cases hxa : x = a
        · subst hxa; simpa using hbadj
        · rw [Function.update_of_ne hxa]
          exact h1 x ((Finset.mem_insert.mp hx).resolve_left hxa)
      · intro x hx
        by_cases hxa : x = a
        · subst hxa; simpa using hbX
        · rw [Function.update_of_ne hxa]
          exact h2 x ((Finset.mem_insert.mp hx).resolve_left hxa)
      · intro x hx
        by_cases hxa : x = a
        · subst hxa; simpa using hbB
        · rw [Function.update_of_ne hxa]
          exact h3 x ((Finset.mem_insert.mp hx).resolve_left hxa)
      · intro x hx y hy hxy
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx hy
        by_cases hxa : x = a
        · by_cases hya : y = a
          · rw [hxa, hya]
          · exfalso
            have hyY : y ∈ Y := hy.resolve_left hya
            rw [hxa, Function.update_self, Function.update_of_ne hya] at hxy
            exact hbY y hyY hxy.symm
        · by_cases hya : y = a
          · exfalso
            have hxY : x ∈ Y := hx.resolve_left hxa
            rw [hya, Function.update_self, Function.update_of_ne hxa] at hxy
            exact hbY x hxY hxy
          · rw [Function.update_of_ne hxa, Function.update_of_ne hya] at hxy
            exact h4 (hx.resolve_left hxa) (hy.resolve_left hya) hxy
  obtain ⟨p, h1, h2, h3, h4⟩ := key X (Finset.Subset.refl _)
  exact ⟨p, h1, h2, h3, h4⟩

lemma edges_of_greedy (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) (X B : Finset V)
    (hdeg : ∀ a ∈ X, 2 * s < G.degree a) (hcard : 2 * X.card + B.card ≤ 2 * s + 2)
    (hXB : Disjoint X B) :
    ∃ E : Finset (Sym2 V), E.card = X.card ∧ (∀ e ∈ E, e ∈ G.edgeSet) ∧
      (∀ e ∈ E, ∀ e' ∈ E, ∀ v, v ∈ e → v ∈ e' → e = e') ∧ (∀ e ∈ E, ∀ v ∈ e, v ∉ B) := by
  obtain ⟨p, h1, h2, h3, h4⟩ := greedy G s X B hdeg hcard
  refine ⟨X.image (fun a => s(a, p a)), ?_, ?_, ?_, ?_⟩
  · apply Finset.card_image_of_injOn
    intro a ha a' ha' h
    simp only at h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨h, -⟩ | ⟨h, h'⟩
    · exact h
    · exact absurd (h ▸ ha) (h2 a' ha')
  · intro e he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    exact h1 a ha
  · intro e he e' he' v hv hv'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp he'
    rw [Sym2.mem_iff] at hv hv'
    have hinj : ∀ x ∈ X, ∀ y ∈ X, p x = p y → x = y := fun x hx y hy h => h4 hx hy h
    rcases hv with rfl | rfl <;> rcases hv' with h | h
    · rw [h]
    · exact absurd (h ▸ ha) (h2 a' ha')
    · exact absurd (h ▸ ha') (h2 a ha)
    · rw [hinj a ha a' ha' h]
  · intro e he v hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    rw [Sym2.mem_iff] at hv
    rcases hv with rfl | rfl
    · exact Finset.disjoint_left.mp hXB ha
    · exact h3 a ha

end TMCAux

theorem solution {n : ℕ} (s : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : TuranMatching.Clique.matchingNumber G ≤ s) :
    #(TuranMatching.ColorCritical.highDeg G s) ≤ s := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨X, hXsub, hXc⟩ := Finset.exists_subset_card_eq (show s + 1 ≤ #(TuranMatching.ColorCritical.highDeg G s) by omega)
  have hdeg : ∀ a ∈ X, 2 * s < G.degree a := by
    intro a ha
    have := hXsub ha
    simpa [TuranMatching.ColorCritical.highDeg] using this
  obtain ⟨E, hE1, hE2, hE3, -⟩ := TMCAux.edges_of_greedy G s X ∅ hdeg (by simp; omega) (Finset.disjoint_empty_right _)
  have := TMCAux.card_le_matchingNumber G E hE2 hE3
  omega
