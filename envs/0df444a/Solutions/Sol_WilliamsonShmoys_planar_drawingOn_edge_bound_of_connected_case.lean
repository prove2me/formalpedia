-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_edge_bound_of_connected_case
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:27:56.128348+00:00
-- url     : https://prove2.me/submissions/4d1080a1-f930-4ba8-8c6b-a4c3542583a0

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

namespace CBHelper

open WilliamsonShmoys

lemma planar_induce {W : Type} [Fintype W] [LinearOrder W] (G : SimpleGraph W)
    (hG : HasPlanarDrawingOn G) (s : Set W) [Fintype s] :
    HasPlanarDrawingOn (G.induce s) := by
  obtain ⟨p, arc, hp, h1, h2⟩ := hG
  refine ⟨fun x => p x.1, fun x y => arc x.1 y.1, hp.comp Subtype.val_injective, ?_, ?_⟩
  · intro u v huv hadj
    obtain ⟨a, b, c, d, e⟩ := h1 u.1 v.1 huv (by simpa using hadj)
    exact ⟨a, b, c, d, fun t ht w => e t ht w.1⟩
  · intro u v x y huv hxy ha hb hne t ht s' hs heq
    refine h2 u.1 v.1 x.1 y.1 huv hxy (by simpa using ha) (by simpa using hb) ?_ t ht s' hs heq
    intro h
    apply hne
    simp only [Prod.mk.injEq] at h ⊢
    exact ⟨Subtype.ext h.1, Subtype.ext h.2⟩

lemma edge_le {W : Type} (G : SimpleGraph W) [Finite W] (s : Set W)
    (hs : ∀ a b, G.Adj a b → a ∈ s → b ∈ s) :
    G.edgeSet.ncard ≤ (G.induce s).edgeSet.ncard + (G.induce sᶜ).edgeSet.ncard := by
  have hsub : G.edgeSet ⊆ (Sym2.map Subtype.val) '' (G.induce s).edgeSet ∪
      (Sym2.map Subtype.val) '' (G.induce sᶜ).edgeSet := by
    intro e he
    induction e using Sym2.ind with
    | h a b =>
      rw [SimpleGraph.mem_edgeSet] at he
      by_cases ha : a ∈ s
      · have hb : b ∈ s := hs a b he ha
        left
        exact ⟨s(⟨a, ha⟩, ⟨b, hb⟩), by simpa using he, by simp⟩
      · have hb : b ∉ s := fun hb => ha (hs b a he.symm hb)
        right
        exact ⟨s(⟨a, ha⟩, ⟨b, hb⟩), by simpa using he, by simp⟩
  calc G.edgeSet.ncard ≤ ((Sym2.map Subtype.val) '' (G.induce s).edgeSet ∪
      (Sym2.map Subtype.val) '' (G.induce sᶜ).edgeSet).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ ((Sym2.map Subtype.val) '' (G.induce s).edgeSet).ncard +
        ((Sym2.map Subtype.val) '' (G.induce sᶜ).edgeSet).ncard := Set.ncard_union_le _ _
    _ ≤ _ := Nat.add_le_add (Set.ncard_image_le (Set.toFinite _))
        (Set.ncard_image_le (Set.toFinite _))

lemma edge_choose {W : Type} [Fintype W] (G : SimpleGraph W) :
    G.edgeSet.ncard ≤ (Fintype.card W).choose 2 := by
  classical
  rw [← G.coe_edgeFinset, Set.ncard_coe_finset]
  exact G.card_edgeFinset_le_card_choose_two

/-- Splitting a disconnected planar graph. -/
lemma split {W : Type} [Fintype W] [LinearOrder W] (G : SimpleGraph W)
    (hne : Nonempty W) (hc : ¬ G.Connected) :
    ∃ s : Set W, (∀ a b, G.Adj a b → a ∈ s → b ∈ s) ∧ 0 < Nat.card s ∧ 0 < Nat.card ↥sᶜ ∧
      Nat.card s + Nat.card ↥sᶜ = Nat.card W := by
  obtain ⟨v⟩ := hne
  have : ∃ w, ¬ G.Reachable v w := by
    by_contra h
    push Not at h
    have : Nonempty W := ⟨v⟩
    exact hc ⟨fun a b => (h a).symm.trans (h b)⟩
  obtain ⟨w, hw⟩ := this
  refine ⟨{x | G.Reachable v x}, fun a b hab ha => ha.trans hab.reachable, ?_, ?_, ?_⟩
  · rw [Nat.card_pos_iff]; exact ⟨⟨⟨v, SimpleGraph.Reachable.refl v⟩⟩, inferInstance⟩
  · rw [Nat.card_pos_iff]; exact ⟨⟨⟨w, hw⟩⟩, inferInstance⟩
  · rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Set.ncard_add_ncard_compl]

lemma key (hConnectedBound :
      ∀ {W : Type} [Fintype W] [LinearOrder W] (G : SimpleGraph W),
        WilliamsonShmoys.HasPlanarDrawingOn G → G.Connected →
        3 ≤ Fintype.card W →
        G.edgeSet.ncard ≤ 3 * Fintype.card W - 6) :
    ∀ n : ℕ, ∀ {W : Type} [Fintype W] [LinearOrder W] (G : SimpleGraph W),
      HasPlanarDrawingOn G → Nat.card W = n → 0 < n → G.edgeSet.ncard + 3 ≤ 3 * n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W _ _ G hG hn hpos
  have hn' := hn
  rw [Nat.card_eq_fintype_card] at hn
  by_cases h2 : n ≤ 2
  · have := edge_choose G
    rw [hn] at this
    have hc2 : n.choose 2 + 3 ≤ 3 * n := by interval_cases n <;> decide
    omega
  by_cases hc : G.Connected
  · have := hConnectedBound G hG hc (by omega)
    omega
  have hne : Nonempty W := by
    rw [← Fintype.card_pos_iff]; omega
  obtain ⟨s, hs, h1, h2', h3⟩ := split G hne hc
  classical
  have e1 := ih (Nat.card s) (by omega) (G.induce s)
    (planar_induce G hG s) rfl h1
  have e2 := ih (Nat.card ↥sᶜ) (by omega) (G.induce sᶜ)
    (planar_induce G hG sᶜ) rfl h2'
  have := edge_le G s hs
  omega

lemma disc (hConnectedBound :
      ∀ {W : Type} [Fintype W] [LinearOrder W] (G : SimpleGraph W),
        WilliamsonShmoys.HasPlanarDrawingOn G → G.Connected →
        3 ≤ Fintype.card W →
        G.edgeSet.ncard ≤ 3 * Fintype.card W - 6)
    {W : Type} [Fintype W] [LinearOrder W] (G : SimpleGraph W)
    (hG : HasPlanarDrawingOn G) (hne : Nonempty W) (hc : ¬ G.Connected) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card W := by
  obtain ⟨s, hs, h1, h2', h3⟩ := split G hne hc
  classical
  have e1 := key hConnectedBound (Nat.card s) (G.induce s) (planar_induce G hG s) rfl h1
  have e2 := key hConnectedBound (Nat.card ↥sᶜ) (G.induce sᶜ) (planar_induce G hG sᶜ) rfl h2'
  have := edge_le G s hs
  rw [Nat.card_eq_fintype_card (α := W)] at h3
  omega

end CBHelper

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hConnectedBound :
      ∀ {W : Type} [Fintype W] [LinearOrder W] (G : SimpleGraph W),
        WilliamsonShmoys.HasPlanarDrawingOn G → G.Connected →
        3 ≤ Fintype.card W →
        G.edgeSet.ncard ≤ 3 * Fintype.card W - 6) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  by_cases hc : K.Connected
  · exact hConnectedBound K hK hc hV
  · have hne : Nonempty V := by rw [← Fintype.card_pos_iff]; omega
    have := CBHelper.disc hConnectedBound K hK hne hc
    omega

