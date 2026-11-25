-- Prove2me | solution 1 for PetersenTheorem.exists_isPerfectMatching_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:39:09.712942+00:00
-- url     : https://prove2.me/submissions/fb1dc3bb-6312-4c06-a509-7df7f24b426b

module
public import Mathlib
public import Definitions.Def_PetersenLib_Petersen
public import Theorems.Thm_PetersenTheorem_three_mul_oddComponents_le

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open PetersenTheorem
variable {V : Type*}
namespace PetersenTheorem
theorem _root_.solution [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) (hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) :
    ∀ e ∈ G.edgeSet, ∃ M : G.Subgraph, M.IsPerfectMatching ∧ e ∈ M.edgeSet := by
  classical
  intro e he
  induction e using Sym2.ind with
  | _ u v =>
  have huv : G.Adj u v := he
  have hne : u ≠ v := huv.ne
  let W : Set V := ({u, v} : Set V)ᶜ
  let G' : SimpleGraph W := G.induce W
  obtain ⟨M', hM'⟩ : ∃ M : G'.Subgraph, M.IsPerfectMatching := by
    rw [tutte]
    intro S hS
    rw [IsTutteViolator] at hS
    have hWuv : ∀ w : W, (w : V) ≠ u ∧ (w : V) ≠ v := by
      intro w
      have h : (w : V) ∉ ({u, v} : Set V) := w.2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h
      exact h
    let T : Finset V := S.toFinset.map (Function.Embedding.subtype _) ∪ {u, v}
    have hdisjT : ∀ w, w ∉ S → (Function.Embedding.subtype _ w : V) ∉ T := by
      intro w hw hwT
      rcases Finset.mem_union.mp hwT with h | h
      · obtain ⟨w', hw', hww'⟩ := Finset.mem_map.mp h
        obtain rfl := Subtype.val_injective hww'
        exact hw (Set.mem_toFinset.mp hw')
      · have := hWuv w
        simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with h | h
        · exact this.1 h
        · exact this.2 h
    have hclosed : ∀ w, w ∉ S → ∀ y, G.Adj (Function.Embedding.subtype _ w) y → y ∉ T →
        ∃ w', Function.Embedding.subtype _ w' = y ∧ G'.Adj w w' ∧ w' ∉ S := by
      intro w hw y hadj hy
      have hyu : y ≠ u := by
        rintro rfl; exact hy (Finset.mem_union_right _ (by simp))
      have hyv : y ≠ v := by
        rintro rfl; exact hy (Finset.mem_union_right _ (by simp))
      have hyW : y ∈ W := by simp [W, hyu, hyv]
      refine ⟨⟨y, hyW⟩, rfl, hadj, fun hS' => hy ?_⟩
      exact Finset.mem_union_left _ (Finset.mem_map_of_mem _ (Set.mem_toFinset.mpr hS'))
    have h := three_mul_oddComponents_le G h3 hb G' S (Function.Embedding.subtype _) T
      hdisjT hclosed
    have hle3 : ∀ y, (G.neighborFinset y \ T).card ≤ 3 := fun y =>
      (Finset.card_le_card Finset.sdiff_subset).trans (by rw [card_neighborFinset_eq_degree, h3 y])
    have hle2 : ∀ a b, G.Adj a b → b ∈ T → (G.neighborFinset a \ T).card ≤ 2 := by
      intro a b hab hbT
      have hsub : G.neighborFinset a \ T ⊆ (G.neighborFinset a).erase b := by
        intro x hx
        rw [Finset.mem_sdiff] at hx
        exact Finset.mem_erase.mpr ⟨fun h => hx.2 (h ▸ hbT), hx.1⟩
      refine (Finset.card_le_card hsub).trans ?_
      rw [Finset.card_erase_of_mem ((mem_neighborFinset _ _ _).mpr hab),
        card_neighborFinset_eq_degree, h3 a]
    have hdisj : Disjoint (S.toFinset.map (Function.Embedding.subtype _)) ({u, v} : Finset V) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨w, -, rfl⟩ := Finset.mem_map.mp hx
      have := hWuv w
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
      rcases hx' with h | h
      · exact this.1 h
      · exact this.2 h
    have key : ∀ g : V → ℕ, (∀ y, g y ≤ 3) → g u ≤ 2 → g v ≤ 2 →
        ∑ y ∈ T, g y ≤ 3 * S.ncard + 4 := by
      intro g hg hgu hgv
      simp only [T]
      rw [Finset.sum_union hdisj, Finset.sum_pair hne]
      have h1 : ∑ x ∈ S.toFinset.map (Function.Embedding.subtype _), g x ≤ S.ncard * 3 := by
        rw [Set.ncard_eq_toFinset_card', ← Finset.card_map (Function.Embedding.subtype _)]
        have h := Finset.sum_le_card_nsmul (S.toFinset.map (Function.Embedding.subtype _)) g 3
          (fun y _ => hg y)
        rw [smul_eq_mul] at h
        exact h
      omega
    have hsum : ∑ y ∈ T, (G.neighborFinset y \ T).card ≤ 3 * S.ncard + 4 :=
      key _ hle3 (hle2 u v huv (Finset.mem_union_right _ (by simp)))
        (hle2 v u huv.symm (Finset.mem_union_right _ (by simp)))
    -- parity
    have hpar := odd_ncard_oddComponents (G := ((⊤ : G'.Subgraph).deleteVerts S).coe)
    have hdiff : Nat.card ↥((⊤ : G'.Subgraph).deleteVerts S).verts + S.ncard = W.ncard := by
      rw [Nat.card_coe_set_eq, Subgraph.deleteVerts_verts, Subgraph.verts_top,
        Set.ncard_sdiff_add_ncard_of_subset (Set.subset_univ S), Set.ncard_univ,
        Nat.card_coe_set_eq]
    have hW : 2 + W.ncard = Nat.card V := by
      rw [← Set.ncard_pair hne]; exact Set.ncard_add_ncard_compl _
    have hV : Even (Nat.card V) := by
      have hs := G.sum_degrees_eq_twice_card_edges
      simp only [h3.degree_eq, Finset.sum_const, smul_eq_mul, Finset.card_univ] at hs
      rw [Nat.card_eq_fintype_card]
      exact Nat.even_iff.mpr (by omega)
    rw [Nat.odd_iff, Nat.odd_iff] at hpar
    rw [Nat.even_iff] at hV
    omega
  rw [Subgraph.isPerfectMatching_iff] at hM'
  let M : G.Subgraph :=
    { verts := Set.univ
      Adj := fun a b => s(a, b) = s(u, v) ∨
        ∃ (ha : a ∈ W) (hb : b ∈ W), M'.Adj ⟨a, ha⟩ ⟨b, hb⟩
      adj_sub := by
        rintro a b (h | ⟨ha, hb, h⟩)
        · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact huv
          · exact huv.symm
        · exact M'.adj_sub h
      edge_vert := fun _ => Set.mem_univ _
      symm := ⟨by
        rintro a b (h | ⟨ha, hb, h⟩)
        · left; rw [Sym2.eq_swap]; exact h
        · exact Or.inr ⟨hb, ha, h.symm⟩⟩ }
  have hWuv : ∀ a, a ∈ W ↔ a ≠ u ∧ a ≠ v := by
    intro a; simp [W, not_or]
  refine ⟨M, ?_, Or.inl rfl⟩
  rw [Subgraph.isPerfectMatching_iff]
  intro a
  by_cases hau : a = u
  · subst hau
    refine ⟨v, Or.inl rfl, ?_⟩
    rintro b (h | ⟨ha, -, -⟩)
    · exact Sym2.congr_right.mp h
    · exact absurd rfl ((hWuv a).mp ha).1
  by_cases hav : a = v
  · subst hav
    refine ⟨u, Or.inl Sym2.eq_swap, ?_⟩
    rintro b (h | ⟨ha, -, -⟩)
    · rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact absurd h1.symm hne
      · exact h2
    · exact absurd rfl ((hWuv a).mp ha).2
  have ha : a ∈ W := (hWuv a).mpr ⟨hau, hav⟩
  obtain ⟨w, hw, huniq⟩ := hM' ⟨a, ha⟩
  refine ⟨w, Or.inr ⟨ha, w.2, hw⟩, ?_⟩
  rintro b (h | ⟨_, hb, h⟩)
  · rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact absurd h1 hau
    · exact absurd h1 hav
  · exact congrArg Subtype.val (huniq ⟨b, hb⟩ h)
end PetersenTheorem
