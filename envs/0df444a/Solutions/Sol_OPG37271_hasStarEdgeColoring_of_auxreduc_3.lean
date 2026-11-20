-- Prove2me | solution 1 for OPG37271.hasStarEdgeColoring_of_auxreduc_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T06:14:40.632321+00:00
-- url     : https://prove2.me/submissions/729833cb-9cec-47ae-90c2-e4f45e10b017

import Definitions.Def_opg37271_star_edge_coloring
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Finset.Card

set_option autoImplicit false

open OPG37271

universe u

private lemma nodup3_elim {α : Type*} {v₀ v₁ v₂ : α} (h : [v₀, v₁, v₂].Nodup) :
    v₀ ≠ v₁ ∧ v₀ ≠ v₂ ∧ v₁ ≠ v₂ := by
  rw [List.nodup_cons, List.nodup_cons] at h
  rcases h with ⟨h0, h1, _⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at h0 h1
  exact ⟨h0.1, h0.2, h1⟩

private lemma nodup4_elim {α : Type*} {v₀ v₁ v₂ v₃ : α} (h : [v₀, v₁, v₂, v₃].Nodup) :
    v₀ ≠ v₁ ∧ v₀ ≠ v₂ ∧ v₀ ≠ v₃ ∧ v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃ := by
  rw [List.nodup_cons] at h
  rcases h with ⟨h0, h123⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at h0
  rcases nodup3_elim h123 with ⟨h12, h13, h23⟩
  exact ⟨h0.1, h0.2.1, h0.2.2, h12, h13, h23⟩

private lemma nodup5_elim {α : Type*} {v₀ v₁ v₂ v₃ v₄ : α} (h : [v₀, v₁, v₂, v₃, v₄].Nodup) :
    v₀ ≠ v₁ ∧ v₀ ≠ v₂ ∧ v₀ ≠ v₃ ∧ v₀ ≠ v₄ ∧
    v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₁ ≠ v₄ ∧ v₂ ≠ v₃ ∧ v₂ ≠ v₄ ∧ v₃ ≠ v₄ := by
  rw [List.nodup_cons] at h
  rcases h with ⟨h0, h1234⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at h0
  rcases nodup4_elim h1234 with ⟨h12, h13, h14, h23, h24, h34⟩
  exact ⟨h0.1, h0.2.1, h0.2.2.1, h0.2.2.2, h12, h13, h14, h23, h24, h34⟩

private lemma nodup3_mk {α : Type*} {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : [a, b, c].Nodup := by
  rw [List.nodup_cons, List.nodup_cons]
  refine ⟨?_, ?_, List.nodup_singleton c⟩
  · simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or]; exact ⟨hab, hac⟩
  · simp only [List.mem_cons, List.mem_nil_iff, or_false]; exact hbc

private lemma sym2_pair_ne {V : Type u} {u₁ v₁ u₂ v₂ : V}
    (h1 : u₁ ≠ u₂) (h2 : u₁ ≠ v₂) : s(u₁, v₁) ≠ s(u₂, v₂) := by
  intro heq
  rw [Sym2.eq_iff] at heq
  rcases heq with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact h1 rfl
  · exact h2 rfl

private lemma c_get_eq_of_sym2 {V : Type u} {G : SimpleGraph V} {K : Type*}
    (c : EdgeColoring G K) {a b u v : V} (hab : G.Adj a b) (huv : G.Adj u v)
    (h : s(a, b) = s(u, v)) :
    c.get a b hab = c.get u v huv :=
  congrArg (fun e : G.edgeSet => c e) (Subtype.ext h)

private lemma c_get_symm {V : Type u} {G : SimpleGraph V} {K : Type*}
    (c : EdgeColoring G K) {a b : V} (hab : G.Adj a b) :
    c.get b a hab.symm = c.get a b hab :=
  c_get_eq_of_sym2 c hab.symm hab Sym2.eq_swap

private lemma c_get_comm {V : Type u} {G : SimpleGraph V} {K : Type*}
    (c : EdgeColoring G K) {a b : V} (hab : G.Adj a b) :
    c.get a b hab = c.get b a hab.symm :=
  c_get_eq_of_sym2 c hab hab.symm Sym2.eq_swap

private def restrictColoring {V : Type u} {H G : SimpleGraph V} {K : Type*}
    (hle : H ≤ G) (c : EdgeColoring G K) : EdgeColoring H K :=
  fun e => c ⟨e.1, SimpleGraph.edgeSet_mono hle e.2⟩

private lemma isStarEdgeColoring_mono {V : Type u} {H G : SimpleGraph V} {K : Type*}
    (hle : H ≤ G) {c : EdgeColoring G K} (hc : IsStarEdgeColoring c) :
    IsStarEdgeColoring (restrictColoring hle c) := by
  rcases hc with ⟨hp, hpa, hcy⟩
  refine ⟨?_, ?_, ?_⟩
  · intro v u w hvu hvw huw
    exact hp v u w (hle hvu) (hle hvw) huw
  · rintro ⟨v₀, v₁, v₂, v₃, v₄, hnd, h01, h12, h23, h34, e1, e2⟩
    exact hpa ⟨v₀, v₁, v₂, v₃, v₄, hnd, hle h01, hle h12, hle h23, hle h34, e1, e2⟩
  · rintro ⟨v₀, v₁, v₂, v₃, hnd, h01, h12, h23, h30, e1, e2⟩
    exact hcy ⟨v₀, v₁, v₂, v₃, hnd, hle h01, hle h12, hle h23, hle h30, e1, e2⟩

private lemma isStarEdgeColoring_insert_edge_priv {V : Type u} {G : SimpleGraph V} {K : Type*}
    (u v : V) (huv : G.Adj u v) (c : EdgeColoring G K)
    (hc_rest : IsStarEdgeColoring (restrictColoring (SimpleGraph.deleteEdges_le {s(u, v)}) c))
    (hdist : ∀ (x y : V) (hxy : G.Adj x y), s(x, y) ≠ s(u, v) →
      (x = u ∨ x = v ∨ y = u ∨ y = v ∨ G.Adj u x ∨ G.Adj v x ∨ G.Adj u y ∨ G.Adj v y) →
      c.get x y hxy ≠ c.get u v huv) :
    IsStarEdgeColoring c := by
  have hadj_rest : ∀ {a b : V}, G.Adj a b → s(a, b) ≠ s(u, v) →
      (G.deleteEdges {s(u, v)}).Adj a b := fun hab hne =>
    SimpleGraph.deleteEdges_adj.mpr ⟨hab, hne⟩
  rcases hc_rest with ⟨hprop, hpath, hcyc⟩
  refine ⟨?_, ?_, ?_⟩
  · intro a b d hab had hbd
    by_cases h1 : s(a, b) = s(u, v)
    · have h2 : s(a, d) ≠ s(u, v) := by
        intro h2
        rw [Sym2.eq_iff] at h1 h2
        rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h2 with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩
        · exact hbd h2b.symm
        · exact huv.ne h2a
        · exact huv.ne h2a.symm
        · exact hbd h2b.symm
      have hdist_ad : (a = u ∨ a = v ∨ d = u ∨ d = v ∨ G.Adj u a ∨ G.Adj v a ∨ G.Adj u d ∨ G.Adj v d) := by
        rw [Sym2.eq_iff] at h1
        rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      have hne := hdist a d had h2 hdist_ad
      rw [c_get_eq_of_sym2 c hab huv h1]
      exact hne.symm
    · by_cases h2 : s(a, d) = s(u, v)
      · have hdist_ab : (a = u ∨ a = v ∨ b = u ∨ b = v ∨ G.Adj u a ∨ G.Adj v a ∨ G.Adj u b ∨ G.Adj v b) := by
          rw [Sym2.eq_iff] at h2
          rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
        have hne := hdist a b hab h1 hdist_ab
        rw [c_get_eq_of_sym2 c had huv h2]
        exact hne
      · exact hprop a b d (hadj_rest hab h1) (hadj_rest had h2) hbd
  · rintro ⟨v₀, v₁, v₂, v₃, v₄, hnodup, h₀₁, h₁₂, h₂₃, h₃₄, hc1, hc2⟩
    rcases nodup5_elim hnodup with ⟨_, h02, h03, _, h12, h13, h14, h23, h24, _⟩
    by_cases e01 : s(v₀, v₁) = s(u, v)
    · have e23 : s(v₂, v₃) ≠ s(u, v) := by
        intro e23
        rw [Sym2.eq_iff] at e01 e23
        rcases e01 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases e23 with ⟨hA, hB⟩ | ⟨hA, hB⟩
        · exact h02 hA.symm
        · exact h03 hB.symm
        · exact h12 hA.symm
        · exact h13 hB.symm
      have hd : v₂ = u ∨ v₂ = v ∨ v₃ = u ∨ v₃ = v ∨ G.Adj u v₂ ∨ G.Adj v v₂ ∨ G.Adj u v₃ ∨ G.Adj v v₃ := by
        rw [Sym2.eq_iff] at e01
        rcases e01 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h₁₂)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h₁₂))))
      exact hdist v₂ v₃ h₂₃ e23 hd (hc1.symm.trans (c_get_eq_of_sym2 c h₀₁ huv e01))
    · by_cases e12 : s(v₁, v₂) = s(u, v)
      · have e34 : s(v₃, v₄) ≠ s(u, v) := by
          intro e34
          rw [Sym2.eq_iff] at e12 e34
          rcases e12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases e34 with ⟨hA, hB⟩ | ⟨hA, hB⟩
          · exact h13 hA.symm
          · exact h14 hB.symm
          · exact h23 hA.symm
          · exact h24 hB.symm
        have hd : v₃ = u ∨ v₃ = v ∨ v₄ = u ∨ v₄ = v ∨ G.Adj u v₃ ∨ G.Adj v v₃ ∨ G.Adj u v₄ ∨ G.Adj v v₄ := by
          rw [Sym2.eq_iff] at e12
          rcases e12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h₂₃)))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h₂₃))))
        exact hdist v₃ v₄ h₃₄ e34 hd (hc2.symm.trans (c_get_eq_of_sym2 c h₁₂ huv e12))
      · by_cases e23 : s(v₂, v₃) = s(u, v)
        · have hd : v₀ = u ∨ v₀ = v ∨ v₁ = u ∨ v₁ = v ∨ G.Adj u v₀ ∨ G.Adj v v₀ ∨ G.Adj u v₁ ∨ G.Adj v v₁ := by
            rw [Sym2.eq_iff] at e23
            rcases e23 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h₁₂.symm))))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h₁₂.symm))))))
          exact hdist v₀ v₁ h₀₁ e01 hd (hc1.trans (c_get_eq_of_sym2 c h₂₃ huv e23))
        · by_cases e34 : s(v₃, v₄) = s(u, v)
          · have hd : v₁ = u ∨ v₁ = v ∨ v₂ = u ∨ v₂ = v ∨ G.Adj u v₁ ∨ G.Adj v v₁ ∨ G.Adj u v₂ ∨ G.Adj v v₂ := by
              rw [Sym2.eq_iff] at e34
              rcases e34 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h₂₃.symm))))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h₂₃.symm))))))
            exact hdist v₁ v₂ h₁₂ e12 hd (hc2.trans (c_get_eq_of_sym2 c h₃₄ huv e34))
          · exact hpath ⟨v₀, v₁, v₂, v₃, v₄, hnodup,
              hadj_rest h₀₁ e01, hadj_rest h₁₂ e12, hadj_rest h₂₃ e23, hadj_rest h₃₄ e34, hc1, hc2⟩
  · rintro ⟨v₀, v₁, v₂, v₃, hnodup, h₀₁, h₁₂, h₂₃, h₃₀, hc1, hc2⟩
    rcases nodup4_elim hnodup with ⟨h01, h02, h03, h12, h13, h23⟩
    by_cases e01 : s(v₀, v₁) = s(u, v)
    · have e23 : s(v₂, v₃) ≠ s(u, v) := by
        intro e23
        rw [Sym2.eq_iff] at e01 e23
        rcases e01 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases e23 with ⟨hA, hB⟩ | ⟨hA, hB⟩
        · exact h02 hA.symm
        · exact h03 hB.symm
        · exact h12 hA.symm
        · exact h13 hB.symm
      have hd : v₂ = u ∨ v₂ = v ∨ v₃ = u ∨ v₃ = v ∨ G.Adj u v₂ ∨ G.Adj v v₂ ∨ G.Adj u v₃ ∨ G.Adj v v₃ := by
        rw [Sym2.eq_iff] at e01
        rcases e01 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h₁₂)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h₁₂))))
      exact hdist v₂ v₃ h₂₃ e23 hd (hc1.symm.trans (c_get_eq_of_sym2 c h₀₁ huv e01))
    · by_cases e12 : s(v₁, v₂) = s(u, v)
      · have e30 : s(v₃, v₀) ≠ s(u, v) := by
          intro e30
          rw [Sym2.eq_iff] at e12 e30
          rcases e12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases e30 with ⟨hA, hB⟩ | ⟨hA, hB⟩
          · exact h13 hA.symm
          · exact h01 hB
          · exact h23 hA.symm
          · exact h02 hB
        have hd : v₃ = u ∨ v₃ = v ∨ v₀ = u ∨ v₀ = v ∨ G.Adj u v₃ ∨ G.Adj v v₃ ∨ G.Adj u v₀ ∨ G.Adj v v₀ := by
          rw [Sym2.eq_iff] at e12
          rcases e12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h₂₃)))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h₂₃))))
        exact hdist v₃ v₀ h₃₀ e30 hd (hc2.symm.trans (c_get_eq_of_sym2 c h₁₂ huv e12))
      · by_cases e23 : s(v₂, v₃) = s(u, v)
        · have hd : v₀ = u ∨ v₀ = v ∨ v₁ = u ∨ v₁ = v ∨ G.Adj u v₀ ∨ G.Adj v v₀ ∨ G.Adj u v₁ ∨ G.Adj v v₁ := by
            rw [Sym2.eq_iff] at e23
            rcases e23 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h₁₂.symm))))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h₁₂.symm))))))
          exact hdist v₀ v₁ h₀₁ e01 hd (hc1.trans (c_get_eq_of_sym2 c h₂₃ huv e23))
        · by_cases e30 : s(v₃, v₀) = s(u, v)
          · have hd : v₁ = u ∨ v₁ = v ∨ v₂ = u ∨ v₂ = v ∨ G.Adj u v₁ ∨ G.Adj v v₁ ∨ G.Adj u v₂ ∨ G.Adj v v₂ := by
              rw [Sym2.eq_iff] at e30
              rcases e30 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h₂₃.symm))))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h₂₃.symm))))))
            exact hdist v₁ v₂ h₁₂ e12 hd (hc2.trans (c_get_eq_of_sym2 c h₃₀ huv e30))
          · exact hcyc ⟨v₀, v₁, v₂, v₃, hnodup,
              hadj_rest h₀₁ e01, hadj_rest h₁₂ e12, hadj_rest h₂₃ e23, hadj_rest h₃₀ e30, hc1, hc2⟩

private lemma isStarEdgeColoring_insert_cut_priv {V : Type u} {G : SimpleGraph V} {K : Type*}
    (A : V → Prop) (c : EdgeColoring G K)
    (hcA : IsStarEdgeColoring (fun e => c ⟨Sym2.map Subtype.val e.1, by rcases e with ⟨⟨a, b⟩, hab⟩; exact hab⟩ :
      EdgeColoring (G.induce {v | A v}) K))
    (hcB : IsStarEdgeColoring (fun e => c ⟨Sym2.map Subtype.val e.1, by rcases e with ⟨⟨a, b⟩, hab⟩; exact hab⟩ :
      EdgeColoring (G.induce {v | ¬ A v}) K))
    (hX_sep : ∀ u₁ v₁ u₂ v₂ : V,
      G.Adj u₁ v₁ → A u₁ → ¬ A v₁ →
      G.Adj u₂ v₂ → A u₂ → ¬ A v₂ →
      s(u₁, v₁) ≠ s(u₂, v₂) →
      u₁ ≠ u₂ ∧ ¬ G.Adj u₁ u₂)
    (hX_B : ∀ u₁ v₁ x y : V,
      (h1 : G.Adj u₁ v₁) → A u₁ → ¬ A v₁ →
      (hxy : G.Adj x y) → (¬ A x ∨ ¬ A y) → s(x, y) ≠ s(u₁, v₁) →
      (x = u₁ ∨ x = v₁ ∨ y = u₁ ∨ y = v₁ ∨
        (G.Adj u₁ x ∧ ¬ A x) ∨ G.Adj v₁ x ∨ (G.Adj u₁ y ∧ ¬ A y) ∨ G.Adj v₁ y) →
      c.get x y hxy ≠ c.get u₁ v₁ h1)
    (hX_A : ∀ u₁ v₁ x y : V,
      (h1 : G.Adj u₁ v₁) → A u₁ → ¬ A v₁ →
      (hxy : G.Adj x y) → A x → A y →
      c.get x y hxy ≠ c.get u₁ v₁ h1) :
    IsStarEdgeColoring c := by
  have hcut_dist : ∀ u₁ v₁ x y : V,
      (h1 : G.Adj u₁ v₁) → A u₁ → ¬ A v₁ →
      (hxy : G.Adj x y) → s(x, y) ≠ s(u₁, v₁) →
      (x = u₁ ∨ x = v₁ ∨ y = u₁ ∨ y = v₁ ∨
        G.Adj u₁ x ∨ G.Adj v₁ x ∨ G.Adj u₁ y ∨ G.Adj v₁ y) →
      c.get x y hxy ≠ c.get u₁ v₁ h1 := by
    intro u₁ v₁ x y h1 hu₁ hv₁ hxy hne hdist
    by_cases hx : A x <;> by_cases hy : A y
    · exact hX_A u₁ v₁ x y h1 hu₁ hv₁ hxy hx hy
    · refine hX_B u₁ v₁ x y h1 hu₁ hv₁ hxy (Or.inr hy) hne ?_
      have hsep := hX_sep u₁ v₁ x y h1 hu₁ hv₁ hxy hx hy hne.symm
      rcases hdist with rfl | rfl | rfl | rfl | hux | hvx | huy | hvy
      · exact absurd rfl hsep.1
      · exact absurd hx hv₁
      · exact absurd hu₁ hy
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact absurd hux hsep.2
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hvx)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨huy, hy⟩))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hvy))))))
    · refine hX_B u₁ v₁ x y h1 hu₁ hv₁ hxy (Or.inl hx) hne ?_
      have hne' : s(u₁, v₁) ≠ s(y, x) := by
        intro h; apply hne; rw [Sym2.eq_swap]; exact h.symm
      have hsep := hX_sep u₁ v₁ y x h1 hu₁ hv₁ hxy.symm hy hx hne'
      rcases hdist with rfl | rfl | rfl | rfl | hux | hvx | huy | hvy
      · exact absurd hu₁ hx
      · exact Or.inr (Or.inl rfl)
      · exact absurd rfl hsep.1
      · exact absurd hy hv₁
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hux, hx⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hvx)))))
      · exact absurd huy hsep.2
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hvy))))))
    · refine hX_B u₁ v₁ x y h1 hu₁ hv₁ hxy (Or.inl hx) hne ?_
      rcases hdist with rfl | rfl | rfl | rfl | hux | hvx | huy | hvy
      · exact absurd hu₁ hx
      · exact Or.inr (Or.inl rfl)
      · exact absurd hu₁ hy
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hux, hx⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hvx)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨huy, hy⟩))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hvy))))))
  have hcut_sym : ∀ u₁ v₁ x y : V,
      (h1 : G.Adj u₁ v₁) → (A u₁ ↔ ¬ A v₁) →
      (hxy : G.Adj x y) → s(x, y) ≠ s(u₁, v₁) →
      (x = u₁ ∨ x = v₁ ∨ y = u₁ ∨ y = v₁ ∨
        G.Adj u₁ x ∨ G.Adj v₁ x ∨ G.Adj u₁ y ∨ G.Adj v₁ y) →
      c.get x y hxy ≠ c.get u₁ v₁ h1 := by
    intro u₁ v₁ x y h1 hdiff hxy hne hdist
    by_cases hu₁ : A u₁
    · exact hcut_dist u₁ v₁ x y h1 hu₁ (hdiff.mp hu₁) hxy hne hdist
    · have hv₁ : A v₁ := by
        by_contra hnv₁
        exact hu₁ (hdiff.mpr hnv₁)
      have hne' : s(x, y) ≠ s(v₁, u₁) := by
        intro h; apply hne; rw [Sym2.eq_swap (a := v₁) (b := u₁)] at h; exact h
      have hdist' : x = v₁ ∨ x = u₁ ∨ y = v₁ ∨ y = u₁ ∨
          G.Adj v₁ x ∨ G.Adj u₁ x ∨ G.Adj v₁ y ∨ G.Adj u₁ y := by
        rcases hdist with h | h | h | h | h | h | h | h <;> tauto
      have hres := hcut_dist v₁ u₁ x y h1.symm hv₁ hu₁ hxy hne' hdist'
      rwa [c_get_symm c h1] at hres
  rcases hcA with ⟨hpA, hpaA, hcyA⟩
  rcases hcB with ⟨hpB, hpaB, hcyB⟩
  refine ⟨?_, ?_, ?_⟩
  · intro a b d hab had hbd
    by_cases h1 : (A a ↔ ¬ A b)
    · exact (hcut_sym a b a d hab h1 had (by intro heq; rw [Sym2.eq_iff] at heq; rcases heq with ⟨_, h2⟩ | ⟨h1', _⟩; exact hbd h2.symm; exact hab.ne h1') (Or.inl rfl)).symm
    · by_cases h2 : (A a ↔ ¬ A d)
      · exact hcut_sym a d a b had h2 hab (by intro heq; rw [Sym2.eq_iff] at heq; rcases heq with ⟨_, h2'⟩ | ⟨h1', _⟩; exact hbd h2'; exact had.ne h1') (Or.inl rfl)
      · by_cases ha : A a
        · have hb : A b := by by_contra hnb; exact h1 ⟨fun _ => hnb, fun _ => ha⟩
          have hd : A d := by by_contra hnd; exact h2 ⟨fun _ => hnd, fun _ => ha⟩
          exact hpA ⟨a, ha⟩ ⟨b, hb⟩ ⟨d, hd⟩ hab had (fun h => hbd (congrArg Subtype.val h))
        · have hb : ¬ A b := fun hb => h1 ⟨fun h => absurd h ha, fun hn => absurd hb hn⟩
          have hd : ¬ A d := fun hd => h2 ⟨fun h => absurd h ha, fun hn => absurd hd hn⟩
          exact hpB ⟨a, ha⟩ ⟨b, hb⟩ ⟨d, hd⟩ hab had (fun h => hbd (congrArg Subtype.val h))
  · rintro ⟨v₀, v₁, v₂, v₃, v₄, hnd, h01, h12, h23, h34, hc1, hc2⟩
    rcases nodup5_elim hnd with ⟨_, n02, _, _, n12, n13, _, n23, _, _⟩
    by_cases e01 : (A v₀ ↔ ¬ A v₁)
    · have hne : s(v₂, v₃) ≠ s(v₀, v₁) := by
        intro h; rw [Sym2.eq_iff] at h; rcases h with ⟨hA, _⟩ | ⟨hA, _⟩ <;> [exact n02 hA.symm; exact n12 hA.symm]
      exact hcut_sym v₀ v₁ v₂ v₃ h01 e01 h23 hne (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h12)))))) hc1.symm
    · by_cases e12 : (A v₁ ↔ ¬ A v₂)
      · have hne : s(v₃, v₄) ≠ s(v₁, v₂) := by
          intro h; rw [Sym2.eq_iff] at h; rcases h with ⟨hA, _⟩ | ⟨hA, _⟩ <;> [exact n13 hA.symm; exact n23 hA.symm]
        exact hcut_sym v₁ v₂ v₃ v₄ h12 e12 h34 hne (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h23)))))) hc2.symm
      · by_cases e23 : (A v₂ ↔ ¬ A v₃)
        · have hne : s(v₀, v₁) ≠ s(v₂, v₃) := by
            intro h; rw [Sym2.eq_iff] at h; rcases h with ⟨hA, _⟩ | ⟨_, hB⟩ <;> [exact n02 hA; exact n12 hB]
          exact hcut_sym v₂ v₃ v₀ v₁ h23 e23 h01 hne (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h12.symm))))))) hc1
        · by_cases e34 : (A v₃ ↔ ¬ A v₄)
          · have hne : s(v₁, v₂) ≠ s(v₃, v₄) := by
              intro h; rw [Sym2.eq_iff] at h; rcases h with ⟨hA, _⟩ | ⟨_, hB⟩ <;> [exact n13 hA; exact n23 hB]
            exact hcut_sym v₃ v₄ v₁ v₂ h34 e34 h12 hne (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h23.symm))))))) hc2
          · by_cases h0 : A v₀
            · have h1 : A v₁ := by by_contra hn; exact e01 ⟨fun _ => hn, fun _ => h0⟩
              have h2 : A v₂ := by by_contra hn; exact e12 ⟨fun _ => hn, fun _ => h1⟩
              have h3 : A v₃ := by by_contra hn; exact e23 ⟨fun _ => hn, fun _ => h2⟩
              have h4 : A v₄ := by by_contra hn; exact e34 ⟨fun _ => hn, fun _ => h3⟩
              refine hpaA ⟨⟨v₀, h0⟩, ⟨v₁, h1⟩, ⟨v₂, h2⟩, ⟨v₃, h3⟩, ⟨v₄, h4⟩, ?_, h01, h12, h23, h34, hc1, hc2⟩
              simpa [List.nodup_cons, Subtype.ext_iff] using hnd
            · have h1 : ¬ A v₁ := fun h => e01 ⟨fun h0' => absurd h0' h0, fun hn => absurd h hn⟩
              have h2 : ¬ A v₂ := fun h => e12 ⟨fun h1' => absurd h1' h1, fun hn => absurd h hn⟩
              have h3 : ¬ A v₃ := fun h => e23 ⟨fun h2' => absurd h2' h2, fun hn => absurd h hn⟩
              have h4 : ¬ A v₄ := fun h => e34 ⟨fun h3' => absurd h3' h3, fun hn => absurd h hn⟩
              refine hpaB ⟨⟨v₀, h0⟩, ⟨v₁, h1⟩, ⟨v₂, h2⟩, ⟨v₃, h3⟩, ⟨v₄, h4⟩, ?_, h01, h12, h23, h34, hc1, hc2⟩
              simpa [List.nodup_cons, Subtype.ext_iff] using hnd
  · rintro ⟨v₀, v₁, v₂, v₃, hnd, h01, h12, h23, h30, hc1, hc2⟩
    rcases nodup4_elim hnd with ⟨_, n02, _, n12, n13, n23⟩
    by_cases e01 : (A v₀ ↔ ¬ A v₁)
    · have hne : s(v₂, v₃) ≠ s(v₀, v₁) := by
        intro h; rw [Sym2.eq_iff] at h; rcases h with ⟨hA, _⟩ | ⟨hA, _⟩ <;> [exact n02 hA.symm; exact n12 hA.symm]
      exact hcut_sym v₀ v₁ v₂ v₃ h01 e01 h23 hne (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h12)))))) hc1.symm
    · by_cases e12 : (A v₁ ↔ ¬ A v₂)
      · have hne : s(v₃, v₀) ≠ s(v₁, v₂) := by
          intro h; rw [Sym2.eq_iff] at h; rcases h with ⟨hA, _⟩ | ⟨hA, _⟩ <;> [exact n13 hA.symm; exact n23 hA.symm]
        exact hcut_sym v₁ v₂ v₃ v₀ h12 e12 h30 hne (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h23)))))) hc2.symm
      · by_cases e23 : (A v₂ ↔ ¬ A v₃)
        · have hne : s(v₀, v₁) ≠ s(v₂, v₃) := by
            intro h; rw [Sym2.eq_iff] at h; rcases h with ⟨hA, _⟩ | ⟨_, hB⟩ <;> [exact n02 hA; exact n12 hB]
          exact hcut_sym v₂ v₃ v₀ v₁ h23 e23 h01 hne (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h12.symm))))))) hc1
        · by_cases e30 : (A v₃ ↔ ¬ A v₀)
          · have hne : s(v₁, v₂) ≠ s(v₃, v₀) := by
              intro h; rw [Sym2.eq_iff] at h; rcases h with ⟨hA, _⟩ | ⟨_, hB⟩ <;> [exact n13 hA; exact n23 hB]
            exact hcut_sym v₃ v₀ v₁ v₂ h30 e30 h12 hne (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h23.symm))))))) hc2
          · by_cases h0 : A v₀
            · have h1 : A v₁ := by by_contra hn; exact e01 ⟨fun _ => hn, fun _ => h0⟩
              have h2 : A v₂ := by by_contra hn; exact e12 ⟨fun _ => hn, fun _ => h1⟩
              have h3 : A v₃ := by by_contra hn; exact e23 ⟨fun _ => hn, fun _ => h2⟩
              refine hcyA ⟨⟨v₀, h0⟩, ⟨v₁, h1⟩, ⟨v₂, h2⟩, ⟨v₃, h3⟩, ?_, h01, h12, h23, h30, hc1, hc2⟩
              simpa [List.nodup_cons, Subtype.ext_iff] using hnd
            · have h1 : ¬ A v₁ := fun h => e01 ⟨fun h0' => absurd h0' h0, fun hn => absurd h hn⟩
              have h2 : ¬ A v₂ := fun h => e12 ⟨fun h1' => absurd h1' h1, fun hn => absurd h hn⟩
              have h3 : ¬ A v₃ := fun h => e23 ⟨fun h2' => absurd h2' h2, fun hn => absurd h hn⟩
              refine hcyB ⟨⟨v₀, h0⟩, ⟨v₁, h1⟩, ⟨v₂, h2⟩, ⟨v₃, h3⟩, ?_, h01, h12, h23, h30, hc1, hc2⟩
              simpa [List.nodup_cons, Subtype.ext_iff] using hnd

/-- If a proper edge coloring has at most one color `k₀` appearing on more than one edge,
then it cannot contain any bicolored `P₄` or `C₄`, so it is a star edge coloring. -/
private lemma isStarEdgeColoring_of_proper_unique_repeat {W : Type*} {H : SimpleGraph W} {K : Type*}
    (c : EdgeColoring H K) (hprop : IsProperEdgeColoring c) (k₀ : K)
    (huniq : ∀ (u₁ v₁ u₂ v₂ : W) (h1 : H.Adj u₁ v₁) (h2 : H.Adj u₂ v₂),
      s(u₁, v₁) ≠ s(u₂, v₂) → c.get u₁ v₁ h1 = c.get u₂ v₂ h2 → c.get u₁ v₁ h1 = k₀) :
    IsStarEdgeColoring c := by
  refine ⟨hprop, ?_, ?_⟩
  · rintro ⟨v₀, v₁, v₂, v₃, v₄, hnd, h01, h12, h23, h34, eq1, eq2⟩
    rcases nodup5_elim hnd with ⟨_, n02, n03, _, _, n13, n14, _, _, _⟩
    have ek1 : c.get v₀ v₁ h01 = k₀ := huniq v₀ v₁ v₂ v₃ h01 h23 (sym2_pair_ne n02 n03) eq1
    have ek2 : c.get v₁ v₂ h12 = k₀ := huniq v₁ v₂ v₃ v₄ h12 h34 (sym2_pair_ne n13 n14) eq2
    apply hprop v₁ v₀ v₂ h01.symm h12 n02
    rw [c_get_symm c h01, ek1, ek2]
  · rintro ⟨v₀, v₁, v₂, v₃, hnd, h01, h12, h23, h30, eq1, eq2⟩
    rcases nodup4_elim hnd with ⟨n01, n02, n03, _, n13, _⟩
    have ek1 : c.get v₀ v₁ h01 = k₀ := huniq v₀ v₁ v₂ v₃ h01 h23 (sym2_pair_ne n02 n03) eq1
    have ek2 : c.get v₁ v₂ h12 = k₀ := huniq v₁ v₂ v₃ v₀ h12 h30 (sym2_pair_ne n13 n01.symm) eq2
    apply hprop v₁ v₀ v₂ h01.symm h12 n02
    rw [c_get_symm c h01, ek1, ek2]

private lemma card_neighborFinset_le_three {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hsub : IsSubcubic G) (v : V) :
    (G.neighborFinset v).card ≤ 3 := by
  have h' : ((G.neighborFinset v : Set V)).encard ≤ 3 := by
    convert hsub v using 1; congr 1; ext x; simp
  rw [Set.encard_coe_eq_coe_finsetCard] at h'
  exact Nat.cast_le.mp h'

private lemma card_neighborFinset_le_two {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {v : V}
    (h : (G.neighborSet v).encard ≤ 2) :
    (G.neighborFinset v).card ≤ 2 := by
  have h' : ((G.neighborFinset v : Set V)).encard ≤ 2 := by
    convert h using 1; congr 1; ext x; simp
  rw [Set.encard_coe_eq_coe_finsetCard] at h'
  exact Nat.cast_le.mp h'

private lemma neighbor_eq_pair {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {v a b : V}
    (hab : a ≠ b) (ha : G.Adj v a) (hb : G.Adj v b)
    (hdeg : (G.neighborSet v).encard ≤ 2) :
    ∀ u : V, G.Adj v u ↔ u = a ∨ u = b := by
  have hcard_le := card_neighborFinset_le_two hdeg
  have hsub_ab : ({a, b} : Finset V) ⊆ G.neighborFinset v := by
    intro u hu
    rw [Finset.mem_insert, Finset.mem_singleton] at hu
    rw [SimpleGraph.mem_neighborFinset]
    rcases hu with rfl | rfl <;> assumption
  have hcard_ab : ({a, b} : Finset V).card = 2 := Finset.card_pair hab
  have heq : ({a, b} : Finset V) = G.neighborFinset v :=
    Finset.eq_of_subset_of_card_le hsub_ab (by omega)
  intro u
  rw [← SimpleGraph.mem_neighborFinset, ← heq, Finset.mem_insert, Finset.mem_singleton]

private lemma neighbor_eq_triple {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {v a b d : V}
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (ha : G.Adj v a) (hb : G.Adj v b) (hd : G.Adj v d)
    (hsub : IsSubcubic G) :
    ∀ u : V, G.Adj v u ↔ u = a ∨ u = b ∨ u = d := by
  have hcard_le := card_neighborFinset_le_three hsub v
  have hsub_abd : ({a, b, d} : Finset V) ⊆ G.neighborFinset v := by
    intro u hu
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hu
    rw [SimpleGraph.mem_neighborFinset]
    rcases hu with rfl | rfl | rfl <;> assumption
  have ha_not : a ∉ ({b, d} : Finset V) := by
    rw [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hab, had⟩
  have hcard_abd : ({a, b, d} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem ha_not, Finset.card_pair hbd]
  have heq : ({a, b, d} : Finset V) = G.neighborFinset v :=
    Finset.eq_of_subset_of_card_le hsub_abd (by omega)
  intro u
  rw [← SimpleGraph.mem_neighborFinset, ← heq, Finset.mem_insert, Finset.mem_insert,
    Finset.mem_singleton]

private lemma at_most_one_other_of_two_mem {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hsub : IsSubcubic G)
    {v x y b₁ b₂ : V} (hxy : x ≠ y) (hvx : G.Adj v x) (hvy : G.Adj v y)
    (hb₁x : b₁ ≠ x) (hb₁y : b₁ ≠ y) (hb₂x : b₂ ≠ x) (hb₂y : b₂ ≠ y)
    (hvb₁ : G.Adj v b₁) (hvb₂ : G.Adj v b₂) : b₁ = b₂ := by
  have heq := neighbor_eq_triple hxy hb₁x.symm hb₁y.symm hvx hvy hvb₁ hsub b₂
  rcases heq.mp hvb₂ with rfl | rfl | rfl
  · exact absurd rfl hb₂x
  · exact absurd rfl hb₂y
  · rfl

private lemma at_most_one_other_of_one_mem {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v x b₁ b₂ : V} (hdeg : (G.neighborSet v).encard ≤ 2) (hvx : G.Adj v x)
    (hb₁x : b₁ ≠ x) (hb₂x : b₂ ≠ x)
    (hvb₁ : G.Adj v b₁) (hvb₂ : G.Adj v b₂) : b₁ = b₂ := by
  have heq := neighbor_eq_pair hb₁x.symm hvx hvb₁ hdeg b₂
  rcases heq.mp hvb₂ with rfl | rfl
  · exact absurd rfl hb₂x
  · rfl

private lemma exists_color_not_mem (S : Finset (Fin 7)) (hS : S.card < 7) :
    ∃ col : Fin 7, col ∉ S := by
  by_contra hnone
  push Not at hnone
  have hle := Finset.card_le_card (s := Finset.univ) (fun x _ => hnone x)
  rw [Finset.card_fin] at hle
  omega

private lemma exists_four_colors_not_mem (UX : Finset (Fin 7)) (hUX : UX.card ≤ 3) :
    ∃ k₁ k₂ k₃ k₄ : Fin 7,
      k₁ ≠ k₂ ∧ k₁ ≠ k₃ ∧ k₁ ≠ k₄ ∧ k₂ ≠ k₃ ∧ k₂ ≠ k₄ ∧ k₃ ≠ k₄ ∧
      k₁ ∉ UX ∧ k₂ ∉ UX ∧ k₃ ∉ UX ∧ k₄ ∉ UX := by
  rcases exists_color_not_mem UX (by omega) with ⟨k₁, hk₁⟩
  have h1 : (insert k₁ UX).card ≤ 4 := le_trans (Finset.card_insert_le _ _) (by omega)
  rcases exists_color_not_mem (insert k₁ UX) (by omega) with ⟨k₂, hk₂⟩
  have h2 : (insert k₂ (insert k₁ UX)).card ≤ 5 := le_trans (Finset.card_insert_le _ _) (by omega)
  rcases exists_color_not_mem (insert k₂ (insert k₁ UX)) (by omega) with ⟨k₃, hk₃⟩
  have h3 : (insert k₃ (insert k₂ (insert k₁ UX))).card ≤ 6 := le_trans (Finset.card_insert_le _ _) (by omega)
  rcases exists_color_not_mem (insert k₃ (insert k₂ (insert k₁ UX))) (by omega) with ⟨k₄, hk₄⟩
  simp only [Finset.mem_insert, not_or] at hk₂ hk₃ hk₄
  exact ⟨k₁, k₂, k₃, k₄,
    fun h => hk₂.1 h.symm, fun h => hk₃.2.1 h.symm, fun h => hk₄.2.2.1 h.symm,
    fun h => hk₃.1 h.symm, fun h => hk₄.2.1 h.symm, fun h => hk₄.1 h.symm,
    hk₁, hk₂.2, hk₃.2.2, hk₄.2.2.2⟩

private lemma exists_three_colors_not_mem (UX : Finset (Fin 7)) (C : Fin 7) (hUX : UX.card ≤ 3) :
    ∃ k₁ k₂ k₃ : Fin 7,
      k₁ ≠ k₂ ∧ k₁ ≠ k₃ ∧ k₂ ≠ k₃ ∧
      k₁ ≠ C ∧ k₂ ≠ C ∧ k₃ ≠ C ∧
      k₁ ∉ UX ∧ k₂ ∉ UX ∧ k₃ ∉ UX := by
  have h0 : (insert C UX).card ≤ 4 := le_trans (Finset.card_insert_le _ _) (by omega)
  rcases exists_color_not_mem (insert C UX) (by omega) with ⟨k₁, hk₁⟩
  have h1 : (insert k₁ (insert C UX)).card ≤ 5 := le_trans (Finset.card_insert_le _ _) (by omega)
  rcases exists_color_not_mem (insert k₁ (insert C UX)) (by omega) with ⟨k₂, hk₂⟩
  have h2 : (insert k₂ (insert k₁ (insert C UX))).card ≤ 6 := le_trans (Finset.card_insert_le _ _) (by omega)
  rcases exists_color_not_mem (insert k₂ (insert k₁ (insert C UX))) (by omega) with ⟨k₃, hk₃⟩
  simp only [Finset.mem_insert, not_or] at hk₁ hk₂ hk₃
  exact ⟨k₁, k₂, k₃,
    fun h => hk₂.1 h.symm, fun h => hk₃.2.1 h.symm, fun h => hk₃.1 h.symm,
    hk₁.1, hk₂.2.1, hk₃.2.2.1, hk₁.2, hk₂.2.2, hk₃.2.2.2⟩

private lemma extend_pendant_seven {V : Type u} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} [DecidableRel H.Adj]
    (hsubH : IsSubcubic H) (u u' : V) (huu' : H.Adj u u')
    (hu_only : ∀ a : V, H.Adj u a → a = u')
    (c' : EdgeColoring (H.deleteEdges {s(u, u')}) (Fin 7))
    (hc' : IsStarEdgeColoring c') :
    ∃ c : EdgeColoring H (Fin 7),
      IsStarEdgeColoring c ∧
      (∀ a b : V, (hab : (H.deleteEdges {s(u, u')}).Adj a b) →
        c.get a b (SimpleGraph.deleteEdges_le {s(u, u')} hab) = c'.get a b hab) ∧
      (∀ a b : V, (hab : (H.deleteEdges {s(u, u')}).Adj a b) →
        (H.deleteEdges {s(u, u')}).Adj u' a →
        c.get a b (SimpleGraph.deleteEdges_le {s(u, u')} hab) ≠ c.get u u' huu') := by
  classical
  let H' := H.deleteEdges {s(u, u')}
  have hH'le : H' ≤ H := SimpleGraph.deleteEdges_le {s(u, u')}
  have hsubH' : IsSubcubic H' :=
    fun v => le_trans (Set.encard_le_encard (SimpleGraph.neighborSet_mono hH'le v)) (hsubH v)
  have hu_none : ∀ a : V, ¬ H'.Adj u a := by
    intro a hua
    rcases SimpleGraph.deleteEdges_adj.mp hua with ⟨huaH, hne⟩
    exact hne (by rw [hu_only a huaH, Set.mem_singleton_iff])
  have hu'_le2 : (H'.neighborFinset u').card ≤ 2 := by
    have hsub_er : H'.neighborFinset u' ⊆ (H.neighborFinset u').erase u := by
      intro a ha
      rw [SimpleGraph.mem_neighborFinset] at ha
      rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset]
      exact ⟨fun hau => hu_none u' (hau ▸ ha.symm), hH'le ha⟩
    have hcard := Finset.card_le_card hsub_er
    rw [Finset.card_erase_of_mem ((SimpleGraph.mem_neighborFinset H u' u).mpr huu'.symm)] at hcard
    have h3 := card_neighborFinset_le_three hsubH u'
    omega
  let S : Finset (Sym2 V) :=
    (H'.neighborFinset u').biUnion fun a => (H'.neighborFinset a).image fun b => s(a, b)
  have hS_lt7 : S.card < 7 := by
    have hle : S.card ≤ 6 := by
      calc S.card
          ≤ ∑ a ∈ H'.neighborFinset u', ((H'.neighborFinset a).image fun b => s(a, b)).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ a ∈ H'.neighborFinset u', (H'.neighborFinset a).card :=
            Finset.sum_le_sum fun a _ => Finset.card_image_le
        _ ≤ ∑ _a ∈ H'.neighborFinset u', 3 :=
            Finset.sum_le_sum fun a _ => card_neighborFinset_le_three hsubH' a
        _ = (H'.neighborFinset u').card * 3 := by simp
        _ ≤ 2 * 3 := Nat.mul_le_mul_right 3 hu'_le2
        _ = 6 := rfl
    omega
  have hS_mem : ∀ x y : V, H.Adj x y → s(x, y) ≠ s(u, u') →
      (x = u ∨ x = u' ∨ y = u ∨ y = u' ∨ H.Adj u x ∨ H.Adj u' x ∨ H.Adj u y ∨ H.Adj u' y) →
      s(x, y) ∈ S := by
    intro x y hxy hne hdist
    have hxy' : H'.Adj x y := SimpleGraph.deleteEdges_adj.mpr ⟨hxy, hne⟩
    have hxu : x ≠ u := fun h => hu_none y (h ▸ hxy')
    have hyu : y ≠ u := fun h => hu_none x (h ▸ hxy'.symm)
    have h_u'_x : x = u' → s(x, y) ∈ S := fun hx => by
      subst hx
      exact Finset.mem_biUnion.mpr ⟨y, (SimpleGraph.mem_neighborFinset H' x y).mpr hxy',
        Finset.mem_image.mpr ⟨x, (SimpleGraph.mem_neighborFinset H' y x).mpr hxy'.symm, Sym2.eq_swap⟩⟩
    have h_u'_y : y = u' → s(x, y) ∈ S := fun hy => by
      subst hy
      exact Finset.mem_biUnion.mpr ⟨x, (SimpleGraph.mem_neighborFinset H' y x).mpr hxy'.symm,
        Finset.mem_image.mpr ⟨y, (SimpleGraph.mem_neighborFinset H' x y).mpr hxy', rfl⟩⟩
    rcases hdist with hx | hx | hy | hy | hux | hu'x | huy | hu'y
    · exact absurd hx hxu
    · exact h_u'_x hx
    · exact absurd hy hyu
    · exact h_u'_y hy
    · exact h_u'_x (hu_only x hux)
    · have hu'x' : H'.Adj u' x := SimpleGraph.deleteEdges_adj.mpr ⟨hu'x, by
        intro heq; rw [Set.mem_singleton_iff, Sym2.eq_iff] at heq
        rcases heq with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact huu'.ne h1.symm
        · exact hxu h2⟩
      exact Finset.mem_biUnion.mpr ⟨x, (SimpleGraph.mem_neighborFinset H' u' x).mpr hu'x',
        Finset.mem_image.mpr ⟨y, (SimpleGraph.mem_neighborFinset H' x y).mpr hxy', rfl⟩⟩
    · exact h_u'_y (hu_only y huy)
    · have hu'y' : H'.Adj u' y := SimpleGraph.deleteEdges_adj.mpr ⟨hu'y, by
        intro heq; rw [Set.mem_singleton_iff, Sym2.eq_iff] at heq
        rcases heq with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact huu'.ne h1.symm
        · exact hyu h2⟩
      exact Finset.mem_biUnion.mpr ⟨y, (SimpleGraph.mem_neighborFinset H' u' y).mpr hu'y',
        Finset.mem_image.mpr ⟨x, (SimpleGraph.mem_neighborFinset H' y x).mpr hxy'.symm, Sym2.eq_swap⟩⟩
  let used : Finset (Fin 7) :=
    S.attach.image fun e => if he : e.1 ∈ H'.edgeSet then c' ⟨e.1, he⟩ else 0
  have hused_lt7 : used.card < 7 := by
    calc used.card ≤ S.attach.card := Finset.card_image_le
      _ = S.card := Finset.card_attach
      _ < 7 := hS_lt7
  rcases exists_color_not_mem used hused_lt7 with ⟨col, hcol⟩
  let c : EdgeColoring H (Fin 7) := fun e =>
    if he : e.1 = s(u, u') then col
    else c' ⟨e.1, by rcases e with ⟨⟨a, b⟩, hab⟩; exact SimpleGraph.deleteEdges_adj.mpr ⟨hab, he⟩⟩
  have hc_agree : ∀ a b : V, (hab : H'.Adj a b) →
      c.get a b (hH'le hab) = c'.get a b hab := by
    intro a b hab
    have hne : s(a, b) ≠ s(u, u') := (SimpleGraph.deleteEdges_adj.mp hab).2
    simp only [SimpleGraph.EdgeLabeling.get, c, dif_neg hne]
  have hc_uu' : c.get u u' huu' = col := by
    simp only [SimpleGraph.EdgeLabeling.get, c, dite_true]
  refine ⟨c, ?_, hc_agree, ?_⟩
  · refine isStarEdgeColoring_insert_edge_priv u u' huu' c ?_ ?_
    · have heq : restrictColoring hH'le c = c' := by
        funext ⟨e, he⟩
        have hne : e ≠ s(u, u') := by rcases e with ⟨a, b⟩; exact (SimpleGraph.deleteEdges_adj.mp he).2
        simp only [restrictColoring, c, dif_neg hne]
      rw [heq]
      exact hc'
    · intro x y hxy hne hdist
      have hmem : s(x, y) ∈ S := hS_mem x y hxy hne hdist
      have hxy' : H'.Adj x y := SimpleGraph.deleteEdges_adj.mpr ⟨hxy, hne⟩
      rw [hc_agree x y hxy', hc_uu']
      intro heq
      apply hcol
      refine Finset.mem_image.mpr ⟨⟨s(x, y), hmem⟩, Finset.mem_attach _ _, ?_⟩
      have hmem_edge : s(x, y) ∈ H'.edgeSet := hxy'
      simp only [dif_pos hmem_edge]
      exact heq
  · intro a b hab hu'a
    have hmem : s(a, b) ∈ S := Finset.mem_biUnion.mpr
      ⟨a, (SimpleGraph.mem_neighborFinset H' u' a).mpr hu'a,
        Finset.mem_image.mpr ⟨b, (SimpleGraph.mem_neighborFinset H' a b).mpr hab, rfl⟩⟩
    rw [hc_agree a b hab, hc_uu']
    intro heq
    apply hcol
    refine Finset.mem_image.mpr ⟨⟨s(a, b), hmem⟩, Finset.mem_attach _ _, ?_⟩
    have hmem_edge : s(a, b) ∈ H'.edgeSet := hab
    simp only [dif_pos hmem_edge]
    exact heq

private lemma insert_optional_port {V : Type u} [Fintype V] {H : SimpleGraph V}
    (hsubH : IsSubcubic H) (p : V)
    (hp_le1 : ∀ b₁ b₂ : V, H.Adj p b₁ → H.Adj p b₂ → b₁ = b₂)
    (c' : EdgeColoring (H.deleteEdges {e : Sym2 V | p ∈ e}) (Fin 7))
    (hc' : IsStarEdgeColoring c') :
    ∃ (c : EdgeColoring H (Fin 7)) (col : Fin 7),
      IsStarEdgeColoring c ∧
      (∀ b : V, (hpb : H.Adj p b) → c.get p b hpb = col) ∧
      (∀ a b : V, (hab : (H.deleteEdges {e : Sym2 V | p ∈ e}).Adj a b) →
        c.get a b (SimpleGraph.deleteEdges_le _ hab) = c'.get a b hab) ∧
      (∀ b x y : V, (hpb : H.Adj p b) →
        (hxy : (H.deleteEdges {e : Sym2 V | p ∈ e}).Adj x y) →
        (H.deleteEdges {e : Sym2 V | p ∈ e}).Adj b x →
        c.get x y (SimpleGraph.deleteEdges_le _ hxy) ≠ c.get p b hpb) := by
  classical
  by_cases hex : ∃ b : V, H.Adj p b
  · rcases hex with ⟨b₀, hpb₀⟩
    have hp_only : ∀ a : V, H.Adj p a → a = b₀ := fun a hpa => hp_le1 a b₀ hpa hpb₀
    have hle1 : H.deleteEdges {s(p, b₀)} ≤ H.deleteEdges {e : Sym2 V | p ∈ e} := by
      intro x y hxy
      rcases SimpleGraph.deleteEdges_adj.mp hxy with ⟨hxyH, hne⟩
      refine SimpleGraph.deleteEdges_adj.mpr ⟨hxyH, ?_⟩
      intro hmem
      change p ∈ s(x, y) at hmem
      rw [Sym2.mem_iff] at hmem
      rcases hmem with rfl | rfl
      · exact hne (by rw [hp_only y hxyH, Set.mem_singleton_iff])
      · exact hne (by rw [hp_only x hxyH.symm, Sym2.eq_swap, Set.mem_singleton_iff])
    have hle2 : H.deleteEdges {e : Sym2 V | p ∈ e} ≤ H.deleteEdges {s(p, b₀)} := by
      intro x y hxy
      rcases SimpleGraph.deleteEdges_adj.mp hxy with ⟨hxyH, hnot⟩
      refine SimpleGraph.deleteEdges_adj.mpr ⟨hxyH, ?_⟩
      intro heq
      apply hnot
      rw [Set.mem_singleton_iff] at heq
      change p ∈ s(x, y)
      rw [heq]
      exact Sym2.mem_mk_left p b₀
    rcases extend_pendant_seven hsubH p b₀ hpb₀ hp_only
        (restrictColoring hle1 c') (isStarEdgeColoring_mono hle1 hc') with
      ⟨c, hc, hc_ag, hc_av⟩
    refine ⟨c, c.get p b₀ hpb₀, hc, ?_, ?_, ?_⟩
    · intro b hpb
      have hb : b = b₀ := hp_only b hpb
      subst hb; rfl
    · intro a b hab
      exact hc_ag a b (hle2 hab)
    · intro b x y hpb hxy hbx
      have hb : b = b₀ := hp_only b hpb
      subst hb
      exact hc_av x y (hle2 hxy) (hle2 hbx)
  · push Not at hex
    have hle : H ≤ H.deleteEdges {e : Sym2 V | p ∈ e} := by
      intro x y hxy
      refine SimpleGraph.deleteEdges_adj.mpr ⟨hxy, ?_⟩
      intro hmem
      change p ∈ s(x, y) at hmem
      rw [Sym2.mem_iff] at hmem
      rcases hmem with rfl | rfl
      · exact hex y hxy
      · exact hex x hxy.symm
    refine ⟨restrictColoring hle c', 0, isStarEdgeColoring_mono hle hc', ?_, ?_, ?_⟩
    · intro b hpb; exact absurd hpb (hex b)
    · intro _ _ _; rfl
    · intro b _ _ hpb; exact absurd hpb (hex b)

private lemma build_BX_coloring {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hsub : IsSubcubic G) (A : V → Prop) (p₁ p₂ p₃ : V)
    (hpA : A p₁ ∧ A p₂ ∧ A p₃) (hp_nd : [p₁, p₂, p₃].Nodup)
    (honly_ports : ∀ u v : V, G.Adj u v → A u → ¬ A v → u = p₁ ∨ u = p₂ ∨ u = p₃)
    (hport_le1 : ∀ u b₁ b₂ : V, A u → G.Adj u b₁ → ¬ A b₁ → G.Adj u b₂ → ¬ A b₂ → b₁ = b₂)
    (hc₀ : HasStarEdgeColoring (G.deleteEdges {e : Sym2 V | ∃ u : V, A u ∧ u ∈ e}) 7) :
    ∃ (c_BX : EdgeColoring (G.deleteEdges {e : Sym2 V | ∀ u : V, u ∈ e → A u}) (Fin 7))
      (UX : Finset (Fin 7)),
      IsStarEdgeColoring c_BX ∧
      UX.card ≤ 3 ∧
      (∀ u v : V, (h : (G.deleteEdges {e : Sym2 V | ∀ w : V, w ∈ e → A w}).Adj u v) →
        A u → ¬ A v → c_BX.get u v h ∈ UX) ∧
      (∀ u₁ v₁ x y : V,
        (h1 : G.Adj u₁ v₁) → A u₁ → ¬ A v₁ →
        (hxy : G.Adj x y) → (¬ A x ∨ ¬ A y) → s(x, y) ≠ s(u₁, v₁) →
        (x = u₁ ∨ x = v₁ ∨ y = u₁ ∨ y = v₁ ∨
          (G.Adj u₁ x ∧ ¬ A x) ∨ G.Adj v₁ x ∨ (G.Adj u₁ y ∧ ¬ A y) ∨ G.Adj v₁ y) →
        (h1_bx : (G.deleteEdges {e : Sym2 V | ∀ w : V, w ∈ e → A w}).Adj u₁ v₁) →
        (hxy_bx : (G.deleteEdges {e : Sym2 V | ∀ w : V, w ∈ e → A w}).Adj x y) →
        c_BX.get x y hxy_bx ≠ c_BX.get u₁ v₁ h1_bx) := by
  classical
  rcases nodup3_elim hp_nd with ⟨np12, np13, np23⟩
  rcases hpA with ⟨hp1A, hp2A, hp3A⟩
  let G₀ := G.deleteEdges {e : Sym2 V | ∃ u : V, A u ∧ u ∈ e}
  let H₃ := G.deleteEdges {e : Sym2 V | ∀ u : V, u ∈ e → A u}
  let H₂ := H₃.deleteEdges {e : Sym2 V | p₃ ∈ e}
  let H₁ := H₂.deleteEdges {e : Sym2 V | p₂ ∈ e}
  let H₀ := H₁.deleteEdges {e : Sym2 V | p₁ ∈ e}

  have hH₃_le : H₃ ≤ G := SimpleGraph.deleteEdges_le _
  have hH₂_le : H₂ ≤ H₃ := SimpleGraph.deleteEdges_le _
  have hH₁_le : H₁ ≤ H₂ := SimpleGraph.deleteEdges_le _
  have hH₀_le : H₀ ≤ H₁ := SimpleGraph.deleteEdges_le _

  have hsub₃ : IsSubcubic H₃ :=
    fun v => le_trans (Set.encard_le_encard (SimpleGraph.neighborSet_mono hH₃_le v)) (hsub v)
  have hsub₂ : IsSubcubic H₂ :=
    fun v => le_trans (Set.encard_le_encard (SimpleGraph.neighborSet_mono hH₂_le v)) (hsub₃ v)
  have hsub₁ : IsSubcubic H₁ :=
    fun v => le_trans (Set.encard_le_encard (SimpleGraph.neighborSet_mono hH₁_le v)) (hsub₂ v)

  have notA_of_H₃_A : ∀ {u b : V}, A u → H₃.Adj u b → ¬ A b := by
    intro u b hu hub hb
    apply (SimpleGraph.deleteEdges_adj.mp hub).2
    intro w hw; rw [Sym2.mem_iff] at hw; rcases hw with rfl | rfl <;> assumption

  have hH₀_le_G₀ : H₀ ≤ G₀ := by
    intro x y hxy
    rcases SimpleGraph.deleteEdges_adj.mp hxy with ⟨hxy1, np1⟩
    rcases SimpleGraph.deleteEdges_adj.mp hxy1 with ⟨hxy2, np2⟩
    rcases SimpleGraph.deleteEdges_adj.mp hxy2 with ⟨hxy3, np3⟩
    rcases SimpleGraph.deleteEdges_adj.mp hxy3 with ⟨hxyG, _⟩
    refine SimpleGraph.deleteEdges_adj.mpr ⟨hxyG, ?_⟩
    rintro ⟨u, huA, humem⟩
    change p₁ ∉ s(x, y) at np1
    change p₂ ∉ s(x, y) at np2
    change p₃ ∉ s(x, y) at np3
    rw [Sym2.mem_iff] at humem
    rcases humem with rfl | rfl
    · have hny : ¬ A y := notA_of_H₃_A huA hxy3
      rcases honly_ports u y hxyG huA hny with rfl | rfl | rfl
      · exact np1 (Sym2.mem_mk_left _ _)
      · exact np2 (Sym2.mem_mk_left _ _)
      · exact np3 (Sym2.mem_mk_left _ _)
    · have hnx : ¬ A x := notA_of_H₃_A huA hxy3.symm
      rcases honly_ports u x hxyG.symm huA hnx with rfl | rfl | rfl
      · exact np1 (Sym2.mem_mk_right _ _)
      · exact np2 (Sym2.mem_mk_right _ _)
      · exact np3 (Sym2.mem_mk_right _ _)

  have adj_H₀_of_notA2 : ∀ {x y : V}, G.Adj x y → ¬ A x → ¬ A y → H₀.Adj x y := by
    intro x y hxy hnx hny
    have h3 : H₃.Adj x y :=
      SimpleGraph.deleteEdges_adj.mpr ⟨hxy, fun hall => hnx (hall x (Sym2.mem_mk_left x y))⟩
    have not_in : ∀ {p : V}, A p → p ∉ s(x, y) := by
      intro p hp hmem; rw [Sym2.mem_iff] at hmem
      rcases hmem with rfl | rfl
      · exact hnx hp
      · exact hny hp
    have h2 : H₂.Adj x y := SimpleGraph.deleteEdges_adj.mpr ⟨h3, not_in hp3A⟩
    have h1 : H₁.Adj x y := SimpleGraph.deleteEdges_adj.mpr ⟨h2, not_in hp2A⟩
    exact SimpleGraph.deleteEdges_adj.mpr ⟨h1, not_in hp1A⟩

  have hp_le1_H₃ : ∀ {u : V}, A u → ∀ b₁ b₂ : V, H₃.Adj u b₁ → H₃.Adj u b₂ → b₁ = b₂ :=
    fun hu b₁ b₂ hb₁ hb₂ =>
      hport_le1 _ b₁ b₂ hu (hH₃_le hb₁) (notA_of_H₃_A hu hb₁) (hH₃_le hb₂) (notA_of_H₃_A hu hb₂)

  rcases hc₀ with ⟨c_init, hc_init⟩
  rcases insert_optional_port hsub₁ p₁
      (fun b₁ b₂ h1 h2 => hp_le1_H₃ hp1A b₁ b₂ (hH₂_le (hH₁_le h1)) (hH₂_le (hH₁_le h2)))
      (restrictColoring hH₀_le_G₀ c_init) (isStarEdgeColoring_mono hH₀_le_G₀ hc_init) with
    ⟨c₁, col₁, hc₁, hcol₁, hc₁_ag, hc₁_av⟩
  rcases insert_optional_port hsub₂ p₂
      (fun b₁ b₂ h1 h2 => hp_le1_H₃ hp2A b₁ b₂ (hH₂_le h1) (hH₂_le h2))
      c₁ hc₁ with
    ⟨c₂, col₂, hc₂, hcol₂, hc₂_ag, hc₂_av⟩
  rcases insert_optional_port hsub₃ p₃
      (fun b₁ b₂ h1 h2 => hp_le1_H₃ hp3A b₁ b₂ h1 h2)
      c₂ hc₂ with
    ⟨c_BX, col₃, hc_BX, hcol₃, hc₃_ag, hc₃_av⟩

  have eq_H₂ : ∀ {a b : V} (h : H₂.Adj a b), c_BX.get a b (hH₂_le h) = c₂.get a b h :=
    fun h => hc₃_ag _ _ h
  have eq_H₁ : ∀ {a b : V} (h : H₁.Adj a b), c_BX.get a b (hH₂_le (hH₁_le h)) = c₁.get a b h :=
    fun h => (eq_H₂ (hH₁_le h)).trans (hc₂_ag _ _ h)

  have adj_p₁_H₁ : ∀ {b : V}, ¬ A b → H₃.Adj p₁ b → H₁.Adj p₁ b := by
    intro b hnb h3
    have h2 : H₂.Adj p₁ b := SimpleGraph.deleteEdges_adj.mpr ⟨h3, fun hm => by
      change p₃ ∈ s(p₁, b) at hm; rw [Sym2.mem_iff] at hm
      rcases hm with h | h; exact np13 h.symm; exact hnb (h ▸ hp3A)⟩
    exact SimpleGraph.deleteEdges_adj.mpr ⟨h2, fun hm => by
      change p₂ ∈ s(p₁, b) at hm; rw [Sym2.mem_iff] at hm
      rcases hm with h | h; exact np12 h.symm; exact hnb (h ▸ hp2A)⟩

  have adj_p₂_H₂ : ∀ {b : V}, ¬ A b → H₃.Adj p₂ b → H₂.Adj p₂ b := by
    intro b hnb h3
    exact SimpleGraph.deleteEdges_adj.mpr ⟨h3, fun hm => by
      change p₃ ∈ s(p₂, b) at hm; rw [Sym2.mem_iff] at hm
      rcases hm with h | h; exact np23 h.symm; exact hnb (h ▸ hp3A)⟩

  let UX : Finset (Fin 7) := {col₁, col₂, col₃}
  have hUX_card : UX.card ≤ 3 := by
    dsimp [UX]
    have h1 := Finset.card_insert_le col₁ ({col₂, col₃} : Finset (Fin 7))
    have h2 := Finset.card_insert_le col₂ ({col₃} : Finset (Fin 7))
    rw [Finset.card_singleton] at h2
    omega

  refine ⟨c_BX, UX, hc_BX, hUX_card, ?_, ?_⟩
  · intro u v huv hu hv
    rcases honly_ports u v (hH₃_le huv) hu hv with hu_eq | hu_eq | hu_eq
    · subst hu_eq
      have h1 := adj_p₁_H₁ hv huv
      rw [c_get_eq_of_sym2 c_BX huv (hH₂_le (hH₁_le h1)) rfl, eq_H₁ h1, hcol₁ v h1]
      simp [UX]
    · subst hu_eq
      have h2 := adj_p₂_H₂ hv huv
      rw [c_get_eq_of_sym2 c_BX huv (hH₂_le h2) rfl, eq_H₂ h2, hcol₂ v h2]
      simp [UX]
    · subst hu_eq
      rw [hcol₃ v huv]
      simp [UX]
  · intro u₁ v₁ x y h1 hu₁ hv₁ hxy _ hne hdist h1_bx hxy_bx
    have dist1_v₁_left : x = v₁ → c_BX.get x y hxy_bx ≠ c_BX.get u₁ v₁ h1_bx := by
      intro hxv; subst hxv
      have hyu : y ≠ u₁ := fun hyu => hne (by subst hyu; exact Sym2.eq_swap)
      rw [c_get_comm c_BX h1_bx]
      exact hc_BX.1 x y u₁ hxy_bx h1_bx.symm hyu
    have dist1_right : y = v₁ → c_BX.get x y hxy_bx ≠ c_BX.get u₁ v₁ h1_bx := by
      intro hyv; subst hyv
      have hxu : x ≠ u₁ := fun hxu => hne (by subst hxu; rfl)
      rw [c_get_comm c_BX hxy_bx, c_get_comm c_BX h1_bx]
      exact hc_BX.1 y x u₁ hxy_bx.symm h1_bx.symm hxu
    have step_v₁ : ∀ {z w : V} (hzw : G.Adj z w) (hzw_bx : H₃.Adj z w),
        s(z, w) ≠ s(u₁, v₁) → G.Adj v₁ z →
        c_BX.get z w hzw_bx ≠ c_BX.get u₁ v₁ h1_bx := by
      intro z w hzw hzw_bx hne_zw hv₁z
      by_cases hzA : A z
      · have hnw : ¬ A w := notA_of_H₃_A hzA hzw_bx
        have hwv : w = v₁ := hport_le1 z w v₁ hzA hzw hnw hv₁z.symm hv₁
        subst hwv
        have hzu : z ≠ u₁ := fun hzu => hne_zw (by subst hzu; rfl)
        rw [c_get_comm c_BX hzw_bx, c_get_comm c_BX h1_bx]
        exact hc_BX.1 w z u₁ hzw_bx.symm h1_bx.symm hzu
      · have hv₁z_0 : H₀.Adj v₁ z := adj_H₀_of_notA2 hv₁z hv₁ hzA
        by_cases hwA : A w
        · have hwu₁ : w ≠ u₁ := by
            intro hwu; subst hwu
            have hzv : z = v₁ := hport_le1 w z v₁ hwA hzw.symm hzA h1 hv₁
            exact hv₁z.ne hzv.symm
          rcases honly_ports u₁ v₁ h1 hu₁ hv₁ with hu_eq | hu_eq | hu_eq <;>
            rcases honly_ports w z hzw.symm hwA hzA with hw_eq | hw_eq | hw_eq
          · exact absurd (hw_eq.trans hu_eq.symm) hwu₁
          · subst hu_eq; subst hw_eq
            have hp1 := adj_p₁_H₁ hv₁ h1_bx
            have hp2 := adj_p₂_H₂ hzA hzw_bx.symm
            have h := hc₂_av z v₁ u₁ hp2 hp1.symm (hH₀_le hv₁z_0).symm
            rw [c_get_comm c_BX hzw_bx, c_get_eq_of_sym2 c_BX hzw_bx.symm (hH₂_le hp2) rfl, eq_H₂ hp2,
              c_get_comm c_BX h1_bx, c_get_eq_of_sym2 c_BX h1_bx.symm (hH₂_le (hH₁_le hp1.symm)) rfl,
              eq_H₂ (hH₁_le hp1.symm)]
            exact h.symm
          · subst hu_eq; subst hw_eq
            have hp1 := adj_p₁_H₁ hv₁ h1_bx
            have h := hc₃_av z v₁ u₁ hzw_bx.symm (hH₁_le hp1.symm) (hH₁_le (hH₀_le hv₁z_0)).symm
            rw [c_get_comm c_BX hzw_bx, c_get_comm c_BX h1_bx,
              c_get_eq_of_sym2 c_BX h1_bx.symm (hH₂_le (hH₁_le hp1.symm)) rfl]
            exact h.symm
          · subst hu_eq; subst hw_eq
            have hp1 := adj_p₁_H₁ hzA hzw_bx.symm
            have hp2 := adj_p₂_H₂ hv₁ h1_bx
            have h := hc₂_av v₁ z w hp2 hp1.symm (hH₀_le hv₁z_0)
            rw [c_get_eq_of_sym2 c_BX hzw_bx (hH₂_le (hH₁_le hp1.symm)) rfl, eq_H₂ (hH₁_le hp1.symm),
              c_get_eq_of_sym2 c_BX h1_bx (hH₂_le hp2) rfl, eq_H₂ hp2]
            exact h
          · exact absurd (hw_eq.trans hu_eq.symm) hwu₁
          · subst hu_eq; subst hw_eq
            have hp2 := adj_p₂_H₂ hv₁ h1_bx
            have h := hc₃_av z v₁ u₁ hzw_bx.symm hp2.symm (hH₁_le (hH₀_le hv₁z_0)).symm
            rw [c_get_comm c_BX hzw_bx, c_get_comm c_BX h1_bx,
              c_get_eq_of_sym2 c_BX h1_bx.symm (hH₂_le hp2.symm) rfl]
            exact h.symm
          · subst hu_eq; subst hw_eq
            have hp1 := adj_p₁_H₁ hzA hzw_bx.symm
            have h := hc₃_av v₁ z w h1_bx (hH₁_le hp1.symm) (hH₁_le (hH₀_le hv₁z_0))
            rw [c_get_eq_of_sym2 c_BX hzw_bx (hH₂_le (hH₁_le hp1.symm)) rfl]
            exact h
          · subst hu_eq; subst hw_eq
            have hp2 := adj_p₂_H₂ hzA hzw_bx.symm
            have h := hc₃_av v₁ z w h1_bx hp2.symm (hH₁_le (hH₀_le hv₁z_0))
            rw [c_get_eq_of_sym2 c_BX hzw_bx (hH₂_le hp2.symm) rfl]
            exact h
          · exact absurd (hw_eq.trans hu_eq.symm) hwu₁
        · have hzw_0 : H₀.Adj z w := adj_H₀_of_notA2 hzw hzA hwA
          rcases honly_ports u₁ v₁ h1 hu₁ hv₁ with hu_eq | hu_eq | hu_eq
          · subst hu_eq
            have hp1 := adj_p₁_H₁ hv₁ h1_bx
            have h := hc₁_av v₁ z w hp1 hzw_0 hv₁z_0
            rw [c_get_eq_of_sym2 c_BX hzw_bx (hH₂_le (hH₁_le (hH₀_le hzw_0))) rfl,
              eq_H₁ (hH₀_le hzw_0),
              c_get_eq_of_sym2 c_BX h1_bx (hH₂_le (hH₁_le hp1)) rfl, eq_H₁ hp1]
            exact h
          · subst hu_eq
            have hp2 := adj_p₂_H₂ hv₁ h1_bx
            have h := hc₂_av v₁ z w hp2 (hH₀_le hzw_0) (hH₀_le hv₁z_0)
            rw [c_get_eq_of_sym2 c_BX hzw_bx (hH₂_le (hH₁_le (hH₀_le hzw_0))) rfl,
              eq_H₂ (hH₁_le (hH₀_le hzw_0)),
              c_get_eq_of_sym2 c_BX h1_bx (hH₂_le hp2) rfl, eq_H₂ hp2]
            exact h
          · subst hu_eq
            have h := hc₃_av v₁ z w h1_bx (hH₁_le (hH₀_le hzw_0)) (hH₁_le (hH₀_le hv₁z_0))
            rw [c_get_eq_of_sym2 c_BX hzw_bx (hH₂_le (hH₁_le (hH₀_le hzw_0))) rfl]
            exact h
    rcases hdist with rfl | hxv | rfl | hyv | ⟨hux, hnx⟩ | hvx | ⟨huy, hny⟩ | hvy
    · have hny : ¬ A y := notA_of_H₃_A hu₁ hxy_bx
      exact absurd (hport_le1 x y v₁ hu₁ hxy hny h1 hv₁ ▸ rfl) hne
    · exact dist1_v₁_left hxv
    · have hnx : ¬ A x := notA_of_H₃_A hu₁ hxy_bx.symm
      exact absurd (hport_le1 y x v₁ hu₁ hxy.symm hnx h1 hv₁ ▸ Sym2.eq_swap) hne
    · exact dist1_right hyv
    · exact dist1_v₁_left (hport_le1 u₁ x v₁ hu₁ hux hnx h1 hv₁)
    · exact step_v₁ hxy hxy_bx hne hvx
    · exact dist1_right (hport_le1 u₁ y v₁ hu₁ huy hny h1 hv₁)
    · rw [c_get_comm c_BX hxy_bx]
      exact step_v₁ hxy.symm hxy_bx.symm (by intro h; apply hne; rwa [Sym2.eq_swap]) hvy

private lemma glue_A_and_BX {V : Type u} {H : SimpleGraph V}
    (A : V → Prop)
    (c_BX : EdgeColoring (H.deleteEdges {e : Sym2 V | ∀ u : V, u ∈ e → A u}) (Fin 7))
    (UX : Finset (Fin 7))
    (hc_BX : IsStarEdgeColoring c_BX)
    (hUX_mem : ∀ u v : V, (h : (H.deleteEdges {e : Sym2 V | ∀ w : V, w ∈ e → A w}).Adj u v) →
      A u → ¬ A v → c_BX.get u v h ∈ UX)
    (hX_B : ∀ u₁ v₁ x y : V,
      (h1 : H.Adj u₁ v₁) → A u₁ → ¬ A v₁ →
      (hxy : H.Adj x y) → (¬ A x ∨ ¬ A y) → s(x, y) ≠ s(u₁, v₁) →
      (x = u₁ ∨ x = v₁ ∨ y = u₁ ∨ y = v₁ ∨
        (H.Adj u₁ x ∧ ¬ A x) ∨ H.Adj v₁ x ∨ (H.Adj u₁ y ∧ ¬ A y) ∨ H.Adj v₁ y) →
      (h1_bx : (H.deleteEdges {e : Sym2 V | ∀ w : V, w ∈ e → A w}).Adj u₁ v₁) →
      (hxy_bx : (H.deleteEdges {e : Sym2 V | ∀ w : V, w ∈ e → A w}).Adj x y) →
      c_BX.get x y hxy_bx ≠ c_BX.get u₁ v₁ h1_bx)
    (hX_sep : ∀ u₁ v₁ u₂ v₂ : V,
      H.Adj u₁ v₁ → A u₁ → ¬ A v₁ →
      H.Adj u₂ v₂ → A u₂ → ¬ A v₂ →
      s(u₁, v₁) ≠ s(u₂, v₂) →
      u₁ ≠ u₂ ∧ ¬ H.Adj u₁ u₂)
    (colA : Sym2 V → Fin 7) (k₀ : Fin 7)
    (hcolA_not_UX : ∀ x y : V, H.Adj x y → A x → A y → colA s(x, y) ∉ UX)
    (hcolA_prop : ∀ v x y : V, A v → A x → A y → H.Adj v x → H.Adj v y → x ≠ y →
      colA s(v, x) ≠ colA s(v, y))
    (hcolA_uniq : ∀ u₁ v₁ u₂ v₂ : V, A u₁ → A v₁ → A u₂ → A v₂ →
      H.Adj u₁ v₁ → H.Adj u₂ v₂ → s(u₁, v₁) ≠ s(u₂, v₂) →
      colA s(u₁, v₁) = colA s(u₂, v₂) → colA s(u₁, v₁) = k₀) :
    ∃ c : EdgeColoring H (Fin 7),
      IsStarEdgeColoring c ∧
      (∀ x y : V, (hxy : H.Adj x y) → A x → A y → c.get x y hxy = colA s(x, y)) ∧
      (∀ x y : V, (hxy_bx : (H.deleteEdges {e : Sym2 V | ∀ w : V, w ∈ e → A w}).Adj x y) →
        c.get x y (SimpleGraph.deleteEdges_le _ hxy_bx) = c_BX.get x y hxy_bx) := by
  classical
  let c : EdgeColoring H (Fin 7) := fun e =>
    if h : ∀ u : V, u ∈ e.1 → A u then colA e.1
    else c_BX ⟨e.1, by
      rcases e with ⟨⟨x, y⟩, hxy⟩
      exact SimpleGraph.deleteEdges_adj.mpr ⟨hxy, h⟩⟩
  have hc_A : ∀ x y : V, (hxy : H.Adj x y) → A x → A y → c.get x y hxy = colA s(x, y) := by
    intro x y hxy hx hy
    have hall : ∀ u : V, u ∈ s(x, y) → A u := by
      intro u hu; rw [Sym2.mem_iff] at hu; rcases hu with rfl | rfl <;> assumption
    simp only [SimpleGraph.EdgeLabeling.get, c, dif_pos hall]
  have hc_notA : ∀ x y : V, (hxy_bx : (H.deleteEdges {e : Sym2 V | ∀ w : V, w ∈ e → A w}).Adj x y) →
      c.get x y (SimpleGraph.deleteEdges_le _ hxy_bx) = c_BX.get x y hxy_bx := by
    intro x y hxy_bx
    have hnot : ¬ (∀ u : V, u ∈ s(x, y) → A u) := (SimpleGraph.deleteEdges_adj.mp hxy_bx).2
    simp only [SimpleGraph.EdgeLabeling.get, c, dif_neg hnot]
  have adj_bx : ∀ {x y : V}, H.Adj x y → (¬ A x ∨ ¬ A y) →
      (H.deleteEdges {e : Sym2 V | ∀ w : V, w ∈ e → A w}).Adj x y := by
    intro x y hxy hna
    refine SimpleGraph.deleteEdges_adj.mpr ⟨hxy, fun hall => ?_⟩
    rcases hna with hx | hy
    · exact hx (hall x (Sym2.mem_mk_left x y))
    · exact hy (hall y (Sym2.mem_mk_right x y))
  refine ⟨c, ?_, hc_A, hc_notA⟩
  refine isStarEdgeColoring_insert_cut_priv A c ?_ ?_ hX_sep ?_ ?_
  · let cA : EdgeColoring (H.induce {v | A v}) (Fin 7) :=
      fun e => c ⟨Sym2.map Subtype.val e.1, by rcases e with ⟨⟨a, b⟩, hab⟩; exact hab⟩
    have cA_eq : ∀ (u v : {v | A v}) (huv : (H.induce {v | A v}).Adj u v),
        cA.get u v huv = colA s(u.1, v.1) :=
      fun u v huv => hc_A u.1 v.1 huv u.2 v.2
    refine isStarEdgeColoring_of_proper_unique_repeat cA ?_ k₀ ?_
    · intro v x y hvx hvy hxy
      rw [cA_eq v x hvx, cA_eq v y hvy]
      exact hcolA_prop v.1 x.1 y.1 v.2 x.2 y.2 hvx hvy (fun h => hxy (Subtype.ext h))
    · intro u₁ v₁ u₂ v₂ h1 h2 hne heq
      rw [cA_eq u₁ v₁ h1] at heq ⊢
      rw [cA_eq u₂ v₂ h2] at heq
      refine hcolA_uniq u₁.1 v₁.1 u₂.1 v₂.1 u₁.2 v₁.2 u₂.2 v₂.2 h1 h2 ?_ heq
      intro hval
      apply hne
      rw [Sym2.eq_iff] at hval ⊢
      rcases hval with ⟨hA, hB⟩ | ⟨hA, hB⟩
      · exact Or.inl ⟨Subtype.ext hA, Subtype.ext hB⟩
      · exact Or.inr ⟨Subtype.ext hA, Subtype.ext hB⟩
  · let cB : EdgeColoring (H.induce {v | ¬ A v}) (Fin 7) :=
      fun e => c ⟨Sym2.map Subtype.val e.1, by rcases e with ⟨⟨a, b⟩, hab⟩; exact hab⟩
    have cB_eq : ∀ (u v : {v | ¬ A v}) (huv : (H.induce {v | ¬ A v}).Adj u v),
        cB.get u v huv = c_BX.get u.1 v.1 (adj_bx huv (Or.inl u.2)) :=
      fun u v huv => hc_notA u.1 v.1 (adj_bx huv (Or.inl u.2))
    rcases hc_BX with ⟨hpBX, hpaBX, hcyBX⟩
    refine ⟨?_, ?_, ?_⟩
    · intro v x y hvx hvy hxy
      rw [cB_eq v x hvx, cB_eq v y hvy]
      exact hpBX v.1 x.1 y.1 _ _ (fun h => hxy (Subtype.ext h))
    · rintro ⟨v₀, v₁, v₂, v₃, v₄, hnd, h01, h12, h23, h34, eq1, eq2⟩
      rw [cB_eq v₀ v₁ h01, cB_eq v₂ v₃ h23] at eq1
      rw [cB_eq v₁ v₂ h12, cB_eq v₃ v₄ h34] at eq2
      refine hpaBX ⟨v₀.1, v₁.1, v₂.1, v₃.1, v₄.1, ?_,
        adj_bx h01 (Or.inl v₀.2), adj_bx h12 (Or.inl v₁.2),
        adj_bx h23 (Or.inl v₂.2), adj_bx h34 (Or.inl v₃.2), eq1, eq2⟩
      simpa [List.nodup_cons, Subtype.ext_iff] using hnd
    · rintro ⟨v₀, v₁, v₂, v₃, hnd, h01, h12, h23, h30, eq1, eq2⟩
      rw [cB_eq v₀ v₁ h01, cB_eq v₂ v₃ h23] at eq1
      rw [cB_eq v₁ v₂ h12, cB_eq v₃ v₀ h30] at eq2
      refine hcyBX ⟨v₀.1, v₁.1, v₂.1, v₃.1, ?_,
        adj_bx h01 (Or.inl v₀.2), adj_bx h12 (Or.inl v₁.2),
        adj_bx h23 (Or.inl v₂.2), adj_bx h30 (Or.inl v₃.2), eq1, eq2⟩
      simpa [List.nodup_cons, Subtype.ext_iff] using hnd
  · intro u₁ v₁ x y h1 hu₁ hv₁ hxy hna hne hdist
    have h1_bx := adj_bx h1 (Or.inr hv₁)
    have hxy_bx := adj_bx hxy hna
    rw [c_get_eq_of_sym2 c hxy (SimpleGraph.deleteEdges_le _ hxy_bx) rfl, hc_notA x y hxy_bx,
      c_get_eq_of_sym2 c h1 (SimpleGraph.deleteEdges_le _ h1_bx) rfl, hc_notA u₁ v₁ h1_bx]
    exact hX_B u₁ v₁ x y h1 hu₁ hv₁ hxy hna hne hdist h1_bx hxy_bx
  · intro u₁ v₁ x y h1 hu₁ hv₁ hxy hx hy
    have h1_bx := adj_bx h1 (Or.inr hv₁)
    rw [hc_A x y hxy hx hy,
      c_get_eq_of_sym2 c h1 (SimpleGraph.deleteEdges_le _ h1_bx) rfl, hc_notA u₁ v₁ h1_bx]
    intro heq
    exact hcolA_not_UX x y hxy hx hy (heq ▸ hUX_mem u₁ v₁ h1_bx hu₁ hv₁)

/-- Template properties for `colA(e) = if e = e₂ then k₂ else if e = e₃ then k₃ else if e = e₄ then k₄ else k₁`:
any collision between distinct edges forces both edges to lie outside `{e₂, e₃, e₄}` and receive `k₁`. -/
private lemma template4_collision {V : Type u} [DecidableEq V]
    (e₂ e₃ e₄ f₁ f₂ : Sym2 V) (k₁ k₂ k₃ k₄ : Fin 7)
    (hk12 : k₁ ≠ k₂) (hk13 : k₁ ≠ k₃) (hk14 : k₁ ≠ k₄)
    (hk23 : k₂ ≠ k₃) (hk24 : k₂ ≠ k₄) (hk34 : k₃ ≠ k₄)
    (hne : f₁ ≠ f₂)
    (heq : (if f₁ = e₂ then k₂ else if f₁ = e₃ then k₃ else if f₁ = e₄ then k₄ else k₁) =
           (if f₂ = e₂ then k₂ else if f₂ = e₃ then k₃ else if f₂ = e₄ then k₄ else k₁)) :
    (if f₁ = e₂ then k₂ else if f₁ = e₃ then k₃ else if f₁ = e₄ then k₄ else k₁) = k₁ ∧
    f₁ ≠ e₂ ∧ f₁ ≠ e₃ ∧ f₁ ≠ e₄ ∧ f₂ ≠ e₂ ∧ f₂ ≠ e₃ ∧ f₂ ≠ e₄ := by
  by_cases h12 : f₁ = e₂ <;> by_cases h22 : f₂ = e₂
  · exact absurd (h12.trans h22.symm) hne
  · rw [if_pos h12, if_neg h22] at heq
    by_cases h23 : f₂ = e₃
    · rw [if_pos h23] at heq; exact absurd heq hk23
    · rw [if_neg h23] at heq
      by_cases h24 : f₂ = e₄
      · rw [if_pos h24] at heq; exact absurd heq hk24
      · rw [if_neg h24] at heq; exact absurd heq.symm hk12
  · rw [if_neg h12, if_pos h22] at heq
    by_cases h13 : f₁ = e₃
    · rw [if_pos h13] at heq; exact absurd heq.symm hk23
    · rw [if_neg h13] at heq
      by_cases h14 : f₁ = e₄
      · rw [if_pos h14] at heq; exact absurd heq.symm hk24
      · rw [if_neg h14] at heq; exact absurd heq hk12
  · rw [if_neg h12, if_neg h22] at heq
    rw [if_neg h12]
    by_cases h13 : f₁ = e₃ <;> by_cases h23 : f₂ = e₃
    · exact absurd (h13.trans h23.symm) hne
    · rw [if_pos h13, if_neg h23] at heq
      by_cases h24 : f₂ = e₄
      · rw [if_pos h24] at heq; exact absurd heq hk34
      · rw [if_neg h24] at heq; exact absurd heq.symm hk13
    · rw [if_neg h13, if_pos h23] at heq
      by_cases h14 : f₁ = e₄
      · rw [if_pos h14] at heq; exact absurd heq.symm hk34
      · rw [if_neg h14] at heq; exact absurd heq hk13
    · rw [if_neg h13, if_neg h23] at heq
      rw [if_neg h13]
      by_cases h14 : f₁ = e₄ <;> by_cases h24 : f₂ = e₄
      · exact absurd (h14.trans h24.symm) hne
      · rw [if_pos h14, if_neg h24] at heq; exact absurd heq.symm hk14
      · rw [if_neg h14, if_pos h24] at heq; exact absurd heq hk14
      · rw [if_neg h14]
        exact ⟨rfl, h12, h13, h14, h22, h23, h24⟩

/-- Complete reduction wrapper for a subgraph `A` with up to 3 mutually non-adjacent ports `p₁, p₂, p₃`
and up to 5 internal edges `{e₁, e₂, e₃, e₄, e₅}` where `e₁` and `e₅` share no endpoint. -/
private lemma reduce_via_four_color_template {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hsub : IsSubcubic G) (A : V → Prop) (p₁ p₂ p₃ : V)
    (hpA : A p₁ ∧ A p₂ ∧ A p₃) (hp_nd : [p₁, p₂, p₃].Nodup)
    (hp_nonadj : ¬ G.Adj p₁ p₂ ∧ ¬ G.Adj p₁ p₃ ∧ ¬ G.Adj p₂ p₃)
    (honly_ports : ∀ u v : V, G.Adj u v → A u → ¬ A v → u = p₁ ∨ u = p₂ ∨ u = p₃)
    (hport_le1 : ∀ u b₁ b₂ : V, A u → G.Adj u b₁ → ¬ A b₁ → G.Adj u b₂ → ¬ A b₂ → b₁ = b₂)
    (e₁ e₂ e₃ e₄ e₅ : Sym2 V)
    (hedges_A : ∀ x y : V, G.Adj x y → A x → A y →
      s(x, y) = e₁ ∨ s(x, y) = e₂ ∨ s(x, y) = e₃ ∨ s(x, y) = e₄ ∨ s(x, y) = e₅)
    (hdisj_15 : ∀ w : V, ¬ (w ∈ e₁ ∧ w ∈ e₅))
    (hc₀ : HasStarEdgeColoring (G.deleteEdges {e : Sym2 V | ∃ u : V, A u ∧ u ∈ e}) 7) :
    HasStarEdgeColoring G 7 := by
  classical
  rcases build_BX_coloring hsub A p₁ p₂ p₃ hpA hp_nd honly_ports hport_le1 hc₀ with
    ⟨c_BX, UX, hc_BX, hUX_card, hUX_mem, hX_B⟩
  rcases exists_four_colors_not_mem UX hUX_card with
    ⟨k₁, k₂, k₃, k₄, hk12, hk13, hk14, hk23, hk24, hk34, hk₁U, hk₂U, hk₃U, hk₄U⟩
  let colA (e : Sym2 V) : Fin 7 :=
    if e = e₂ then k₂ else if e = e₃ then k₃ else if e = e₄ then k₄ else k₁
  have hX_sep : ∀ u₁ v₁ u₂ v₂ : V,
      G.Adj u₁ v₁ → A u₁ → ¬ A v₁ →
      G.Adj u₂ v₂ → A u₂ → ¬ A v₂ →
      s(u₁, v₁) ≠ s(u₂, v₂) → u₁ ≠ u₂ ∧ ¬ G.Adj u₁ u₂ := by
    intro u₁ v₁ u₂ v₂ h1 hu₁ hv₁ h2 hu₂ hv₂ hne
    have hu_ne : u₁ ≠ u₂ := by
      intro heq; subst heq
      have hv_eq : v₁ = v₂ := hport_le1 u₁ v₁ v₂ hu₁ h1 hv₁ h2 hv₂
      exact hne (by subst hv_eq; rfl)
    refine ⟨hu_ne, ?_⟩
    rcases honly_ports u₁ v₁ h1 hu₁ hv₁ with rfl | rfl | rfl <;>
      rcases honly_ports u₂ v₂ h2 hu₂ hv₂ with rfl | rfl | rfl
    · exact absurd rfl hu_ne
    · exact hp_nonadj.1
    · exact hp_nonadj.2.1
    · exact fun h => hp_nonadj.1 h.symm
    · exact absurd rfl hu_ne
    · exact hp_nonadj.2.2
    · exact fun h => hp_nonadj.2.1 h.symm
    · exact fun h => hp_nonadj.2.2 h.symm
    · exact absurd rfl hu_ne
  rcases glue_A_and_BX A c_BX UX hc_BX hUX_mem hX_B hX_sep colA k₁
      (by
        intro x y _ _ _
        dsimp [colA]
        split_ifs
        · exact hk₂U
        · exact hk₃U
        · exact hk₄U
        · exact hk₁U)
      (by
        intro v x y hv hx hy hvx hvy hxy heq
        have hne_e : s(v, x) ≠ s(v, y) := by
          intro h; rw [Sym2.eq_iff] at h
          rcases h with ⟨_, h2⟩ | ⟨h1, _⟩
          · exact hxy h2
          · exact hvy.ne h1
        rcases template4_collision e₂ e₃ e₄ s(v, x) s(v, y) k₁ k₂ k₃ k₄
            hk12 hk13 hk14 hk23 hk24 hk34 hne_e heq with
          ⟨_, n12, n13, n14, n22, n23, n24⟩
        have m1 : s(v, x) = e₁ ∨ s(v, x) = e₅ := by
          rcases hedges_A v x hvx hv hx with h | h | h | h | h
          · exact Or.inl h
          · exact absurd h n12
          · exact absurd h n13
          · exact absurd h n14
          · exact Or.inr h
        have m2 : s(v, y) = e₁ ∨ s(v, y) = e₅ := by
          rcases hedges_A v y hvy hv hy with h | h | h | h | h
          · exact Or.inl h
          · exact absurd h n22
          · exact absurd h n23
          · exact absurd h n24
          · exact Or.inr h
        rcases m1 with h1 | h1 <;> rcases m2 with h2 | h2
        · exact hne_e (h1.trans h2.symm)
        · exact hdisj_15 v ⟨h1 ▸ Sym2.mem_mk_left v x, h2 ▸ Sym2.mem_mk_left v y⟩
        · exact hdisj_15 v ⟨h2 ▸ Sym2.mem_mk_left v y, h1 ▸ Sym2.mem_mk_left v x⟩
        · exact hne_e (h1.trans h2.symm))
      (by
        intro u₁ v₁ u₂ v₂ _ _ _ _ _ _ hne heq
        exact (template4_collision e₂ e₃ e₄ s(u₁, v₁) s(u₂, v₂) k₁ k₂ k₃ k₄
          hk12 hk13 hk14 hk23 hk24 hk34 hne heq).1) with
    ⟨c, hc, _, _⟩
  exact ⟨c, hc⟩


/-- Third auxiliary reducible configuration in Figure 1 (`page=4` of `figauxreduc.pdf`):
a `4`-cycle `a₀ - a₁ - a₂ - a₃ - a₀` where opposite vertices `a₀` and `a₂` have degree at most `2`
and there is no chord `a₁a₃`. -/
theorem solution {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hsub : IsSubcubic G) (a₀ a₁ a₂ a₃ : V)
    (hnd : [a₀, a₁, a₂, a₃].Nodup)
    (h01 : G.Adj a₀ a₁) (h12 : G.Adj a₁ a₂) (h23 : G.Adj a₂ a₃) (h30 : G.Adj a₃ a₀)
    (ha₀ : (G.neighborSet a₀).encard ≤ 2) (ha₂ : (G.neighborSet a₂).encard ≤ 2)
    (hna13 : ¬ G.Adj a₁ a₃)
    (hc' : HasStarEdgeColoring
      (G.deleteEdges {e : Sym2 V | a₀ ∈ e ∨ a₁ ∈ e ∨ a₂ ∈ e ∨ a₃ ∈ e}) 7) :
    HasStarEdgeColoring G 7 := by
  classical
  rcases nodup4_elim hnd with ⟨n01, n02, n03, n12, n13, n23⟩
  let A : V → Prop := fun v => v = a₀ ∨ v = a₁ ∨ v = a₂ ∨ v = a₃
  have adj_a₀ : ∀ u : V, G.Adj a₀ u ↔ u = a₁ ∨ u = a₃ :=
    neighbor_eq_pair n13 h01 h30.symm ha₀
  have adj_a₂ : ∀ u : V, G.Adj a₂ u ↔ u = a₁ ∨ u = a₃ :=
    neighbor_eq_pair n13 h12.symm h23 ha₂
  have hna02 : ¬ G.Adj a₀ a₂ := by
    intro h; rcases (adj_a₀ a₂).mp h with h1 | h1
    · exact n12 h1.symm
    · exact n23 h1
  have heq_G₀ : G.deleteEdges {e : Sym2 V | ∃ u : V, A u ∧ u ∈ e} =
      G.deleteEdges {e : Sym2 V | a₀ ∈ e ∨ a₁ ∈ e ∨ a₂ ∈ e ∨ a₃ ∈ e} := by
    congr 1; ext e; dsimp only [A]; change (∃ u : V, (u = a₀ ∨ u = a₁ ∨ u = a₂ ∨ u = a₃) ∧ u ∈ e) ↔ _
    constructor
    · rintro ⟨u, rfl | rfl | rfl | rfl, hu⟩
      · exact Or.inl hu
      · exact Or.inr (Or.inl hu)
      · exact Or.inr (Or.inr (Or.inl hu))
      · exact Or.inr (Or.inr (Or.inr hu))
    · rintro (h | h | h | h)
      · exact ⟨a₀, Or.inl rfl, h⟩
      · exact ⟨a₁, Or.inr (Or.inl rfl), h⟩
      · exact ⟨a₂, Or.inr (Or.inr (Or.inl rfl)), h⟩
      · exact ⟨a₃, Or.inr (Or.inr (Or.inr rfl)), h⟩
  -- Pass p₃ = a₀? Wait: G.Adj a₁ a₀ holds! We need ¬ G.Adj p₁ p₃ and ¬ G.Adj p₂ p₃!
  -- Wait: neither a₀ nor a₂ has ANY outside neighbors, AND ¬ G.Adj a₀ a₂, wait: G.Adj a₁ a₂ ALSO holds!
  -- Aha! In reduce_via_four_color_template, hp_nonadj was ONLY used when BOTH u₁ and u₂ had outside edges!
  -- Even simpler: let's check build_BX_coloring directly for auxreduc_3 (passing p₃ = a₀ to build_BX_coloring, which does NOT take hp_nonadj!)!
  rcases build_BX_coloring hsub A a₁ a₃ a₀
      ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr (Or.inr rfl)), Or.inl rfl⟩
      (nodup3_mk n13 n01.symm n03.symm)
      (by
        intro u v huv hu hv
        rcases hu with rfl | rfl | rfl | rfl
        · rcases (adj_a₀ v).mp huv with rfl | rfl
          · exact absurd (Or.inr (Or.inl rfl)) hv
          · exact absurd (Or.inr (Or.inr (Or.inr rfl))) hv
        · exact Or.inl rfl
        · rcases (adj_a₂ v).mp huv with rfl | rfl
          · exact absurd (Or.inr (Or.inl rfl)) hv
          · exact absurd (Or.inr (Or.inr (Or.inr rfl))) hv
        · exact Or.inr (Or.inl rfl))
      (by
        intro u b₁ b₂ hu hub₁ hnb₁ hub₂ hnb₂
        rcases hu with rfl | rfl | rfl | rfl
        · rcases (adj_a₀ b₁).mp hub₁ with rfl | rfl
          · exact absurd (Or.inr (Or.inl rfl)) hnb₁
          · exact absurd (Or.inr (Or.inr (Or.inr rfl))) hnb₁
        · exact at_most_one_other_of_two_mem hsub n02 h01.symm h12
            (fun h => hnb₁ (Or.inl h)) (fun h => hnb₁ (Or.inr (Or.inr (Or.inl h))))
            (fun h => hnb₂ (Or.inl h)) (fun h => hnb₂ (Or.inr (Or.inr (Or.inl h))))
            hub₁ hub₂
        · rcases (adj_a₂ b₁).mp hub₁ with rfl | rfl
          · exact absurd (Or.inr (Or.inl rfl)) hnb₁
          · exact absurd (Or.inr (Or.inr (Or.inr rfl))) hnb₁
        · exact at_most_one_other_of_two_mem hsub n02 h30 h23.symm
            (fun h => hnb₁ (Or.inl h)) (fun h => hnb₁ (Or.inr (Or.inr (Or.inl h))))
            (fun h => hnb₂ (Or.inl h)) (fun h => hnb₂ (Or.inr (Or.inr (Or.inl h))))
            hub₁ hub₂)
      (heq_G₀.symm ▸ hc') with
    ⟨c_BX, UX, hc_BX, hUX_card, hUX_mem, hX_B⟩
  rcases exists_four_colors_not_mem UX hUX_card with
    ⟨k₁, k₂, k₃, k₄, hk12, hk13, hk14, hk23, hk24, hk34, hk₁U, hk₂U, hk₃U, hk₄U⟩
  let colA (e : Sym2 V) : Fin 7 :=
    if e = s(a₂, a₃) then k₂ else if e = s(a₀, a₃) then k₃ else if e = s(a₁, a₂) then k₄ else k₁
  have hX_sep : ∀ u₁ v₁ u₂ v₂ : V,
      G.Adj u₁ v₁ → A u₁ → ¬ A v₁ →
      G.Adj u₂ v₂ → A u₂ → ¬ A v₂ →
      s(u₁, v₁) ≠ s(u₂, v₂) → u₁ ≠ u₂ ∧ ¬ G.Adj u₁ u₂ := by
    intro u₁ v₁ u₂ v₂ h1 hu₁ hv₁ h2 hu₂ hv₂ hne
    have u_13 : ∀ {u v : V}, G.Adj u v → A u → ¬ A v → u = a₁ ∨ u = a₃ := by
      intro u v huv hu hv
      rcases hu with rfl | rfl | rfl | rfl
      · rcases (adj_a₀ v).mp huv with rfl | rfl
        · exact absurd (Or.inr (Or.inl rfl)) hv
        · exact absurd (Or.inr (Or.inr (Or.inr rfl))) hv
      · exact Or.inl rfl
      · rcases (adj_a₂ v).mp huv with rfl | rfl
        · exact absurd (Or.inr (Or.inl rfl)) hv
        · exact absurd (Or.inr (Or.inr (Or.inr rfl))) hv
      · exact Or.inr rfl
    have hu_ne : u₁ ≠ u₂ := by
      intro heq; subst heq
      rcases u_13 h1 hu₁ hv₁ with rfl | rfl
      · have hv_eq := at_most_one_other_of_two_mem hsub n02 h01.symm h12
          (fun h => hv₁ (Or.inl h)) (fun h => hv₁ (Or.inr (Or.inr (Or.inl h))))
          (fun h => hv₂ (Or.inl h)) (fun h => hv₂ (Or.inr (Or.inr (Or.inl h)))) h1 h2
        exact hne (by subst hv_eq; rfl)
      · have hv_eq := at_most_one_other_of_two_mem hsub n02 h30 h23.symm
          (fun h => hv₁ (Or.inl h)) (fun h => hv₁ (Or.inr (Or.inr (Or.inl h))))
          (fun h => hv₂ (Or.inl h)) (fun h => hv₂ (Or.inr (Or.inr (Or.inl h)))) h1 h2
        exact hne (by subst hv_eq; rfl)
    refine ⟨hu_ne, ?_⟩
    rcases u_13 h1 hu₁ hv₁ with rfl | rfl <;> rcases u_13 h2 hu₂ hv₂ with rfl | rfl
    · exact absurd rfl hu_ne
    · exact hna13
    · exact fun h => hna13 h.symm
    · exact absurd rfl hu_ne
  have hedges_A : ∀ x y : V, G.Adj x y → A x → A y →
      s(x, y) = s(a₀, a₁) ∨ s(x, y) = s(a₂, a₃) ∨ s(x, y) = s(a₀, a₃) ∨ s(x, y) = s(a₁, a₂) := by
    intro x y hxy hx hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl
    · exact absurd hxy.ne (fun h => h rfl)
    · exact Or.inl rfl
    · exact absurd hxy hna02
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inl Sym2.eq_swap
    · exact absurd hxy.ne (fun h => h rfl)
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact absurd hxy hna13
    · exact absurd hxy.symm hna02
    · exact Or.inr (Or.inr (Or.inr Sym2.eq_swap))
    · exact absurd hxy.ne (fun h => h rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl Sym2.eq_swap))
    · exact absurd hxy.symm hna13
    · exact Or.inr (Or.inl Sym2.eq_swap)
    · exact absurd hxy.ne (fun h => h rfl)
  rcases glue_A_and_BX A c_BX UX hc_BX hUX_mem hX_B hX_sep colA k₁
      (by
        intro x y _ _ _; dsimp [colA]; split_ifs
        · exact hk₂U
        · exact hk₃U
        · exact hk₄U
        · exact hk₁U)
      (by
        intro v x y hv hx hy hvx hvy hxy heq
        have hne_e : s(v, x) ≠ s(v, y) := by
          intro h; rw [Sym2.eq_iff] at h
          rcases h with ⟨_, h2⟩ | ⟨h1, _⟩; exact hxy h2; exact hvy.ne h1
        rcases template4_collision s(a₂, a₃) s(a₀, a₃) s(a₁, a₂) s(v, x) s(v, y) k₁ k₂ k₃ k₄
            hk12 hk13 hk14 hk23 hk24 hk34 hne_e heq with
          ⟨_, n12', n13', n14', n22', n23', n24'⟩
        have e1 : s(v, x) = s(a₀, a₁) := by
          rcases hedges_A v x hvx hv hx with h | h | h | h
          · exact h
          · exact absurd h n12'
          · exact absurd h n13'
          · exact absurd h n14'
        have e2 : s(v, y) = s(a₀, a₁) := by
          rcases hedges_A v y hvy hv hy with h | h | h | h
          · exact h
          · exact absurd h n22'
          · exact absurd h n23'
          · exact absurd h n24'
        exact hne_e (e1.trans e2.symm))
      (by
        intro u₁ v₁ u₂ v₂ _ _ _ _ _ _ hne heq
        exact (template4_collision s(a₂, a₃) s(a₀, a₃) s(a₁, a₂) s(u₁, v₁) s(u₂, v₂) k₁ k₂ k₃ k₄
          hk12 hk13 hk14 hk23 hk24 hk34 hne heq).1) with
    ⟨c, hc, _, _⟩
  exact ⟨c, hc⟩

