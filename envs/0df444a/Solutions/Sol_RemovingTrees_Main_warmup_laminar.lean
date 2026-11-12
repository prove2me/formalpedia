-- Prove2me | solution 1 for RemovingTrees.Main.warmup_laminar
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T17:42:50.227054+00:00
-- url     : https://prove2.me/submissions/679be284-ff0d-415f-b056-d7c5b916aadb

import Mathlib
import Definitions.Def_RemovingTrees_Main_GraphModel
import Theorems.Thm_RemovingTrees_Main_fundamental_cuts_noncrossing

section
set_option autoImplicit false

namespace RemovingTrees.Dev.WarmupLaminar
open RemovingTrees.Main

theorem mem_treeUnion {m : ℕ} (l : List (Finset (Fin m))) (x : Fin m) :
    x ∈ treeUnion l ↔ ∃ T ∈ l, x ∈ T := by
  have : ∀ (init : Finset (Fin m)), x ∈ l.foldl (fun H T => H ∪ T) init ↔ x ∈ init ∨ ∃ T ∈ l, x ∈ T := by
    induction l with
    | nil => intro init; simp
    | cons a t ih =>
      intro init
      simp only [List.foldl_cons, ih, Finset.mem_union, List.mem_cons]
      constructor
      · rintro ((h | h) | ⟨T, hT, hx⟩)
        · exact Or.inl h
        · exact Or.inr ⟨a, Or.inl rfl, h⟩
        · exact Or.inr ⟨T, Or.inr hT, hx⟩
      · rintro (h | ⟨T, hT | hT, hx⟩)
        · exact Or.inl (Or.inl h)
        · subst hT; exact Or.inl (Or.inr hx)
        · exact Or.inr ⟨T, hT, hx⟩
  have := this ∅
  simpa [treeUnion] using this

theorem cut_split {n m : ℕ} (G : MultiGraph n m) (R T : Finset (Fin m)) (S : Finset (Fin n))
    (h : T ⊆ R) : (cut G R S).card = (cut G T S).card + (cut G (R \ T) S).card := by
  have hd : Disjoint (cut G T S) (cut G (R \ T) S) := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    simp only [cut, Finset.mem_filter, Finset.mem_sdiff] at h1 h2
    exact h2.1.2 h1.1
  have : cut G R S = cut G T S ∪ cut G (R \ T) S := by
    ext e
    simp only [cut, Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases he : e ∈ T
      · exact Or.inl ⟨he, h2⟩
      · exact Or.inr ⟨⟨h1, he⟩, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨⟨h1, _⟩, h2⟩)
      · exact ⟨h h1, h2⟩
      · exact ⟨h1, h2⟩
  rw [this, Finset.card_union_of_disjoint hd]

theorem sum_le {n m : ℕ} (G : MultiGraph n m) (S : Finset (Fin n)) :
    ∀ (L : List (Finset (Fin m))) (R : Finset (Fin m)), L.Pairwise Disjoint →
      (∀ T ∈ L, T ⊆ R) → (L.map fun T => (cut G T S).card).sum ≤ (cut G R S).card := by
  intro L
  induction L with
  | nil => intro R _ _; simp
  | cons T L ih =>
    intro R hp hs
    rw [List.pairwise_cons] at hp
    have hTR : T ⊆ R := hs T (by simp)
    have h1 : (L.map fun T => (cut G T S).card).sum ≤ (cut G (R \ T) S).card := by
      apply ih _ hp.2
      intro U hU x hx
      rw [Finset.mem_sdiff]
      refine ⟨hs U (by simp [hU]) hx, ?_⟩
      intro hxT
      exact Finset.disjoint_left.mp (hp.1 U hU) hxT hx
    rw [List.map_cons, List.sum_cons, cut_split G R T S hTR]
    omega

theorem pair_ge {n m : ℕ} (G : MultiGraph n m) (hn : 2 ≤ n) (T : Finset (Fin m)) (hT : Tree G T)
    (S₁ S₂ : Finset (Fin n)) (h1 : NontrivialShore S₁) (h2 : NontrivialShore S₂)
    (hc : Cross S₁ S₂) : 3 ≤ (cut G T S₁).card + (cut G T S₂).card := by
  have a1 : 1 ≤ (cut G T S₁).card := Finset.card_pos.mpr (hT.1 S₁ h1)
  have a2 : 1 ≤ (cut G T S₂).card := Finset.card_pos.mpr (hT.1 S₂ h2)
  by_contra hlt
  have e1 : (cut G T S₁).card = 1 := by omega
  have e2 : (cut G T S₂).card = 1 := by omega
  exact RemovingTrees.Main.fundamental_cuts_noncrossing G hn T hT S₁ S₂ e1 e2 hc

theorem sum_ge {n m : ℕ} (G : MultiGraph n m) (hn : 2 ≤ n) (S₁ S₂ : Finset (Fin n))
    (h1 : NontrivialShore S₁) (h2 : NontrivialShore S₂) (hc : Cross S₁ S₂) :
    ∀ L : List (Finset (Fin m)), (∀ T ∈ L, Tree G T) →
      3 * L.length ≤ (L.map fun T => (cut G T S₁).card).sum + (L.map fun T => (cut G T S₂).card).sum := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons T L ih =>
    intro h
    have := pair_ge G hn T (h T (by simp)) S₁ S₂ h1 h2 hc
    have := ih (fun U hU => h U (by simp [hU]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega


theorem laminar {n m : ℕ} (G : MultiGraph n m) (hn : 2 ≤ n)
    (k C : ℕ) (hk : 0 < k) (hC : 0 < C) (heven : Even k) (hG : CutLower G Finset.univ k)
    (ts : List (Finset (Fin m))) (hpack : Packing G Finset.univ ts)
    (hlen : ts.length = k / 2) (hreserve : 44*C ≤ k / 2) (root : Fin n) :
    SteinerCutDominants.IsLaminar
      (rootedLowCuts G (Finset.univ \ treeUnion (ts.take (44*C))) root
        ((3:ℝ)/4*k - 66*C)) := by
  intro S1 h1 S2 h2 hint
  obtain ⟨hI, hAB, hBA⟩ := hint
  simp only [rootedLowCuts, Finset.mem_filter, Finset.mem_powerset] at h1 h2
  obtain ⟨-, hr1, hc1⟩ := h1
  obtain ⟨-, hr2, hc2⟩ := h2
  set R := Finset.univ \ treeUnion (ts.take (44*C)) with hR
  have ns1 : NontrivialShore S1 := ⟨hI.mono Finset.inter_subset_left, fun h => hr1 (h ▸ Finset.mem_univ _)⟩
  have ns2 : NontrivialShore S2 := ⟨hI.mono Finset.inter_subset_right, fun h => hr2 (h ▸ Finset.mem_univ _)⟩
  have hc : Cross S1 S2 := ⟨hAB, hBA, hI, ⟨root, by simp [hr1, hr2]⟩⟩
  have hpk := hpack.2
  have hpt := hpack.1
  rw [← List.take_append_drop (44*C) ts] at hpk
  rw [List.pairwise_append] at hpk
  obtain ⟨-, hpd, hcross⟩ := hpk
  have hsub : ∀ T ∈ ts.drop (44*C), T ⊆ R := by
    intro T hT x hx
    rw [hR, Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [mem_treeUnion]
    rintro ⟨U, hU, hxU⟩
    exact Finset.disjoint_left.mp (hcross U hU T hT) hxU hx
  have htree : ∀ T ∈ ts.drop (44*C), Tree G T := fun T hT =>
    (hpt T (List.mem_of_mem_drop hT)).2
  have s1 := sum_le G S1 _ R hpd hsub
  have s2 := sum_le G S2 _ R hpd hsub
  have s3 := sum_ge G hn S1 S2 ns1 ns2 hc _ htree
  rw [List.length_drop, hlen] at s3
  obtain ⟨j, hj⟩ := heven
  have hk2 : k / 2 = j := by omega
  rw [hk2] at s3 hreserve
  have hcast : ((j - 44*C : ℕ) : ℝ) = (j:ℝ) - 44*C := by
    rw [Nat.cast_sub hreserve]; push_cast; ring
  have key : (3:ℝ) * ((j - 44*C : ℕ) : ℝ) ≤ ((cut G R S1).card : ℝ) + ((cut G R S2).card : ℝ) := by
    have : 3 * (j - 44*C) ≤ (cut G R S1).card + (cut G R S2).card := by omega
    exact_mod_cast this
  rw [hcast] at key
  have hkr : (k:ℝ) = 2 * j := by exact_mod_cast hj.trans (by ring)
  rw [hkr] at hc1 hc2
  linarith

end RemovingTrees.Dev.WarmupLaminar

namespace RemovingTrees.Main
theorem chk_warmup_laminar {n m : ℕ} (G : MultiGraph n m) (hn : 2 ≤ n)
    (k C : ℕ) (hk : 0 < k) (hC : 0 < C) (heven : Even k) (hG : CutLower G Finset.univ k)
    (ts : List (Finset (Fin m))) (hpack : Packing G Finset.univ ts)
    (hlen : ts.length = k / 2) (hreserve : 44*C ≤ k / 2) (root : Fin n) :
    SteinerCutDominants.IsLaminar
      (rootedLowCuts G (Finset.univ \ treeUnion (ts.take (44*C))) root
        ((3:ℝ)/4*k - 66*C)) :=
  RemovingTrees.Dev.WarmupLaminar.laminar G hn k C hk hC heven hG ts hpack hlen hreserve root
end RemovingTrees.Main
end

theorem solution : type_of% @RemovingTrees.Main.chk_warmup_laminar := @RemovingTrees.Main.chk_warmup_laminar
