-- Prove2me | solution 1 for OPG37271.hasStarEdgeColoring_of_deg2_path4_distinct
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T05:42:17.954824+00:00
-- url     : https://prove2.me/submissions/7f666edb-d325-4fc3-a9ad-689b5e2c93ab

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

private lemma nodup4_rot {α : Type*} {v₀ v₁ v₂ v₃ : α}
    (h : [v₀, v₁, v₂, v₃].Nodup) : [v₁, v₂, v₃, v₀].Nodup := by
  rcases nodup4_elim h with ⟨h01, h02, h03, h12, h13, h23⟩
  rw [List.nodup_cons, List.nodup_cons, List.nodup_cons]
  refine ⟨?_, ⟨?_, ⟨?_, List.nodup_singleton v₀⟩⟩⟩
  · simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or]
    exact ⟨h12, h13, h01.symm⟩
  · simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or]
    exact ⟨h23, h02.symm⟩
  · simp only [List.mem_cons, List.mem_nil_iff, or_false]
    exact h03.symm

private lemma nodup5_rev {α : Type*} {v₀ v₁ v₂ v₃ v₄ : α}
    (h : [v₀, v₁, v₂, v₃, v₄].Nodup) : [v₄, v₃, v₂, v₁, v₀].Nodup := by
  rcases nodup5_elim h with ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34⟩
  rw [List.nodup_cons, List.nodup_cons, List.nodup_cons, List.nodup_cons]
  refine ⟨?_, ⟨?_, ⟨?_, ⟨?_, List.nodup_singleton v₀⟩⟩⟩⟩
  · simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or]
    exact ⟨h34.symm, h24.symm, h14.symm, h04.symm⟩
  · simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or]
    exact ⟨h23.symm, h13.symm, h03.symm⟩
  · simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or]
    exact ⟨h12.symm, h02.symm⟩
  · simp only [List.mem_cons, List.mem_nil_iff, or_false]
    exact h01.symm

private lemma nodup5_init {α : Type*} {v₀ v₁ v₂ v₃ v₄ : α}
    (h : [v₀, v₁, v₂, v₃, v₄].Nodup) : [v₀, v₁, v₂, v₃].Nodup := by
  rcases nodup5_elim h with ⟨h01, h02, h03, _, h12, h13, _, h23, _, _⟩
  rw [List.nodup_cons, List.nodup_cons, List.nodup_cons]
  refine ⟨?_, ⟨?_, ⟨?_, List.nodup_singleton v₃⟩⟩⟩
  · simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or]
    exact ⟨h01, h02, h03⟩
  · simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or]
    exact ⟨h12, h13⟩
  · simp only [List.mem_cons, List.mem_nil_iff, or_false]
    exact h23

private lemma not_nodup_three_of_two {α : Type*} {a b u₀ u₁ u₂ : α}
    (hnd : [u₀, u₁, u₂].Nodup)
    (h0 : u₀ = a ∨ u₀ = b) (h1 : u₁ = a ∨ u₁ = b) (h2 : u₂ = a ∨ u₂ = b) : False := by
  rcases nodup3_elim hnd with ⟨n01, n02, n12⟩
  rcases h0 with rfl | rfl <;> rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
  · exact n01 rfl
  · exact n01 rfl
  · exact n02 rfl
  · exact n12 rfl
  · exact n12 rfl
  · exact n02 rfl
  · exact n01 rfl
  · exact n01 rfl

private lemma not_nodup_four_of_three {α : Type*} {a b d v₀ v₁ v₂ v₃ : α}
    (hnd : [v₀, v₁, v₂, v₃].Nodup)
    (h0 : v₀ = a ∨ v₀ = b ∨ v₀ = d) (h1 : v₁ = a ∨ v₁ = b ∨ v₁ = d)
    (h2 : v₂ = a ∨ v₂ = b ∨ v₂ = d) (h3 : v₃ = a ∨ v₃ = b ∨ v₃ = d) : False := by
  rcases nodup4_elim hnd with ⟨n01, n02, n03, _⟩
  have h123 : [v₁, v₂, v₃].Nodup := (List.nodup_cons.mp hnd).2
  rcases h0 with rfl | rfl | rfl
  · exact not_nodup_three_of_two h123
      (h1.resolve_left n01.symm)
      (h2.resolve_left n02.symm)
      (h3.resolve_left n03.symm)
  · have drop_b : ∀ {u : α}, v₀ ≠ u → (u = a ∨ u = v₀ ∨ u = d) → (u = a ∨ u = d) := by
      intro u hne hu
      rcases hu with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact absurd rfl hne
      · exact Or.inr rfl
    exact not_nodup_three_of_two h123 (drop_b n01 h1) (drop_b n02 h2) (drop_b n03 h3)
  · have drop_d : ∀ {u : α}, v₀ ≠ u → (u = a ∨ u = b ∨ u = v₀) → (u = a ∨ u = b) := by
      intro u hne hu
      rcases hu with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd rfl hne
    exact not_nodup_three_of_two h123 (drop_d n01 h1) (drop_d n02 h2) (drop_d n03 h3)

private lemma not_nodup_five_of_four {α : Type*} {a b d e v₀ v₁ v₂ v₃ v₄ : α}
    (hnd : [v₀, v₁, v₂, v₃, v₄].Nodup)
    (h0 : v₀ = a ∨ v₀ = b ∨ v₀ = d ∨ v₀ = e)
    (h1 : v₁ = a ∨ v₁ = b ∨ v₁ = d ∨ v₁ = e)
    (h2 : v₂ = a ∨ v₂ = b ∨ v₂ = d ∨ v₂ = e)
    (h3 : v₃ = a ∨ v₃ = b ∨ v₃ = d ∨ v₃ = e)
    (h4 : v₄ = a ∨ v₄ = b ∨ v₄ = d ∨ v₄ = e) : False := by
  rcases nodup5_elim hnd with ⟨n01, n02, n03, n04, _⟩
  have h1234 : [v₁, v₂, v₃, v₄].Nodup := (List.nodup_cons.mp hnd).2
  rcases h0 with rfl | rfl | rfl | rfl
  · exact not_nodup_four_of_three h1234
      (h1.resolve_left n01.symm)
      (h2.resolve_left n02.symm)
      (h3.resolve_left n03.symm)
      (h4.resolve_left n04.symm)
  · have drop2 : ∀ {u : α}, v₀ ≠ u → (u = a ∨ u = v₀ ∨ u = d ∨ u = e) → (u = a ∨ u = d ∨ u = e) := by
      intro u hne hu
      rcases hu with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact absurd rfl hne
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    exact not_nodup_four_of_three h1234 (drop2 n01 h1) (drop2 n02 h2) (drop2 n03 h3) (drop2 n04 h4)
  · have drop3 : ∀ {u : α}, v₀ ≠ u → (u = a ∨ u = b ∨ u = v₀ ∨ u = e) → (u = a ∨ u = b ∨ u = e) := by
      intro u hne hu
      rcases hu with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact absurd rfl hne
      · exact Or.inr (Or.inr rfl)
    exact not_nodup_four_of_three h1234 (drop3 n01 h1) (drop3 n02 h2) (drop3 n03 h3) (drop3 n04 h4)
  · have drop4 : ∀ {u : α}, v₀ ≠ u → (u = a ∨ u = b ∨ u = d ∨ u = v₀) → (u = a ∨ u = b ∨ u = d) := by
      intro u hne hu
      rcases hu with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
      · exact absurd rfl hne
    exact not_nodup_four_of_three h1234 (drop4 n01 h1) (drop4 n02 h2) (drop4 n03 h3) (drop4 n04 h4)

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

private lemma exists_color_not_mem (S : Finset (Fin 7)) (hS : S.card < 7) :
    ∃ col : Fin 7, col ∉ S := by
  by_contra hnone
  push Not at hnone
  have hle := Finset.card_le_card (s := Finset.univ) (fun x _ => hnone x)
  rw [Finset.card_fin] at hle
  omega

private lemma card_insert2_union2 (A B : Finset (Fin 7)) (x y : Fin 7)
    (hA : A.card ≤ 2) (hB : B.card ≤ 2) :
    (insert x (insert y (A ∪ B))).card < 7 := by
  have h1 := Finset.card_insert_le x (insert y (A ∪ B))
  have h2 := Finset.card_insert_le y (A ∪ B)
  have h3 := Finset.card_union_le A B
  omega

private lemma card_insert4_set (A : Finset (Fin 7)) (x y z w : Fin 7)
    (hA : A.card ≤ 2) :
    (insert x (insert y (insert z (insert w A)))).card < 7 := by
  have h1 := Finset.card_insert_le x (insert y (insert z (insert w A)))
  have h2 := Finset.card_insert_le y (insert z (insert w A))
  have h3 := Finset.card_insert_le z (insert w A)
  have h4 := Finset.card_insert_le w A
  omega

private lemma card_triple_lt (x y z : Fin 7) :
    ({x, y, z} : Finset (Fin 7)).card < 7 := by
  have h1 := Finset.card_insert_le x ({y, z} : Finset (Fin 7))
  have h2 := Finset.card_insert_le y ({z} : Finset (Fin 7))
  rw [Finset.card_singleton] at h2
  omega

private lemma exists_qpr_colors
    (cs ct cu cv : Fin 7)
    (Ew Ex Ey Ez : Finset (Fin 7))
    (hEw : Ew.card ≤ 2) (hEx : Ex.card ≤ 2) (hEy : Ey.card ≤ 2) (hEz : Ez.card ≤ 2) :
    ∃ cq cp cr : Fin 7,
      cq ≠ ct ∧ cq ≠ cu ∧ cq ∉ Ex ∧ cq ∉ Ey ∧
      cp ≠ cs ∧ cp ≠ cq ∧ cp ≠ ct ∧
      cr ≠ cv ∧ cr ≠ cq ∧ cr ≠ cu ∧
      (cs = ct → cp ∉ Ew ∧ cp ∉ Ex) ∧
      (cu = cv → cr ∉ Ey ∧ cr ∉ Ez) ∧
      (cs = cq → cp ∉ Ew ∧ cp ≠ cu ∧ cp ≠ cr) ∧
      (cv = cq → cr ∉ Ez ∧ cr ≠ ct ∧ cr ≠ cp) := by
  rcases exists_color_not_mem (insert ct (insert cu (Ex ∪ Ey)))
      (card_insert2_union2 Ex Ey ct cu hEx hEy) with ⟨cq, hcq⟩
  simp only [Finset.mem_insert, Finset.mem_union, not_or] at hcq
  rcases hcq with ⟨hcq_ct, hcq_cu, hcq_Ex, hcq_Ey⟩
  by_cases hsq : cs = cq <;> by_cases hvq : cv = cq
  · -- Case 4: cs = cq ∧ cv = cq
    have hcs_ct : cs ≠ ct := fun h => hcq_ct (hsq.symm.trans h)
    have hcu_cv : cu ≠ cv := fun h => hcq_cu (hvq.symm.trans h.symm)
    rcases exists_color_not_mem (insert cq (insert ct (insert cu (insert cq Ew))))
        (card_insert4_set Ew cq ct cu cq hEw) with ⟨cp, hcp⟩
    simp only [Finset.mem_insert, not_or] at hcp
    rcases hcp with ⟨hcp_cq, hcp_ct, hcp_cu, _, hcp_Ew⟩
    rcases exists_color_not_mem (insert cq (insert cu (insert ct (insert cp Ez))))
        (card_insert4_set Ez cq cu ct cp hEz) with ⟨cr, hcr⟩
    simp only [Finset.mem_insert, not_or] at hcr
    rcases hcr with ⟨hcr_cq, hcr_cu, hcr_ct, hcr_cp, hcr_Ez⟩
    refine ⟨cq, cp, cr, hcq_ct, hcq_cu, hcq_Ex, hcq_Ey,
      fun h => hcp_cq (h.trans hsq), hcp_cq, hcp_ct,
      fun h => hcr_cq (h.trans hvq), hcr_cq, hcr_cu,
      fun h => absurd h hcs_ct,
      fun h => absurd h hcu_cv,
      fun _ => ⟨hcp_Ew, hcp_cu, fun h => hcr_cp h.symm⟩,
      fun _ => ⟨hcr_Ez, hcr_ct, hcr_cp⟩⟩
  · -- Case 2: cs = cq ∧ cv ≠ cq
    have hcs_ct : cs ≠ ct := fun h => hcq_ct (hsq.symm.trans h)
    have hex_r : ∃ cr : Fin 7, cr ≠ cv ∧ cr ≠ cq ∧ cr ≠ cu ∧ (cu = cv → cr ∉ Ey ∧ cr ∉ Ez) := by
      by_cases huv : cu = cv
      · rcases exists_color_not_mem (insert cv (insert cq (Ey ∪ Ez)))
            (card_insert2_union2 Ey Ez cv cq hEy hEz) with ⟨cr, hcr⟩
        simp only [Finset.mem_insert, Finset.mem_union, not_or] at hcr
        rcases hcr with ⟨hcr_cv, hcr_cq, hcr_Ey, hcr_Ez⟩
        exact ⟨cr, hcr_cv, hcr_cq, fun h => hcr_cv (h.trans huv), fun _ => ⟨hcr_Ey, hcr_Ez⟩⟩
      · rcases exists_color_not_mem {cv, cq, cu} (card_triple_lt cv cq cu) with ⟨cr, hcr⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcr
        rcases hcr with ⟨hcr_cv, hcr_cq, hcr_cu⟩
        exact ⟨cr, hcr_cv, hcr_cq, hcr_cu, fun h => absurd h huv⟩
    rcases hex_r with ⟨cr, hcr_cv, hcr_cq, hcr_cu, hcr_uv⟩
    rcases exists_color_not_mem (insert cs (insert ct (insert cu (insert cr Ew))))
        (card_insert4_set Ew cs ct cu cr hEw) with ⟨cp, hcp⟩
    simp only [Finset.mem_insert, not_or] at hcp
    rcases hcp with ⟨hcp_cs, hcp_ct, hcp_cu, hcp_cr, hcp_Ew⟩
    refine ⟨cq, cp, cr, hcq_ct, hcq_cu, hcq_Ex, hcq_Ey,
      hcp_cs, fun h => hcp_cs (h.trans hsq.symm), hcp_ct,
      hcr_cv, hcr_cq, hcr_cu,
      fun h => absurd h hcs_ct,
      hcr_uv,
      fun _ => ⟨hcp_Ew, hcp_cu, hcp_cr⟩,
      fun h => absurd h hvq⟩
  · -- Symmetric Case 2: cs ≠ cq ∧ cv = cq
    have hcu_cv : cu ≠ cv := fun h => hcq_cu (hvq.symm.trans h.symm)
    have hex_p : ∃ cp : Fin 7, cp ≠ cs ∧ cp ≠ cq ∧ cp ≠ ct ∧ (cs = ct → cp ∉ Ew ∧ cp ∉ Ex) := by
      by_cases hst : cs = ct
      · rcases exists_color_not_mem (insert cs (insert cq (Ew ∪ Ex)))
            (card_insert2_union2 Ew Ex cs cq hEw hEx) with ⟨cp, hcp⟩
        simp only [Finset.mem_insert, Finset.mem_union, not_or] at hcp
        rcases hcp with ⟨hcp_cs, hcp_cq, hcp_Ew, hcp_Ex⟩
        exact ⟨cp, hcp_cs, hcp_cq, fun h => hcp_cs (h.trans hst.symm), fun _ => ⟨hcp_Ew, hcp_Ex⟩⟩
      · rcases exists_color_not_mem {cs, cq, ct} (card_triple_lt cs cq ct) with ⟨cp, hcp⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcp
        rcases hcp with ⟨hcp_cs, hcp_cq, hcp_ct⟩
        exact ⟨cp, hcp_cs, hcp_cq, hcp_ct, fun h => absurd h hst⟩
    rcases hex_p with ⟨cp, hcp_cs, hcp_cq, hcp_ct, hcp_st⟩
    rcases exists_color_not_mem (insert cv (insert cu (insert ct (insert cp Ez))))
        (card_insert4_set Ez cv cu ct cp hEz) with ⟨cr, hcr⟩
    simp only [Finset.mem_insert, not_or] at hcr
    rcases hcr with ⟨hcr_cv, hcr_cu, hcr_ct, hcr_cp, hcr_Ez⟩
    refine ⟨cq, cp, cr, hcq_ct, hcq_cu, hcq_Ex, hcq_Ey,
      hcp_cs, hcp_cq, hcp_ct,
      hcr_cv, fun h => hcr_cv (h.trans hvq.symm), hcr_cu,
      hcp_st,
      fun h => absurd h hcu_cv,
      fun h => absurd h hsq,
      fun _ => ⟨hcr_Ez, hcr_ct, hcr_cp⟩⟩
  · -- Cases 1 & 3: cs ≠ cq ∧ cv ≠ cq
    have hex_p : ∃ cp : Fin 7, cp ≠ cs ∧ cp ≠ cq ∧ cp ≠ ct ∧ (cs = ct → cp ∉ Ew ∧ cp ∉ Ex) := by
      by_cases hst : cs = ct
      · rcases exists_color_not_mem (insert cs (insert cq (Ew ∪ Ex)))
            (card_insert2_union2 Ew Ex cs cq hEw hEx) with ⟨cp, hcp⟩
        simp only [Finset.mem_insert, Finset.mem_union, not_or] at hcp
        rcases hcp with ⟨hcp_cs, hcp_cq, hcp_Ew, hcp_Ex⟩
        exact ⟨cp, hcp_cs, hcp_cq, fun h => hcp_cs (h.trans hst.symm), fun _ => ⟨hcp_Ew, hcp_Ex⟩⟩
      · rcases exists_color_not_mem {cs, cq, ct} (card_triple_lt cs cq ct) with ⟨cp, hcp⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcp
        rcases hcp with ⟨hcp_cs, hcp_cq, hcp_ct⟩
        exact ⟨cp, hcp_cs, hcp_cq, hcp_ct, fun h => absurd h hst⟩
    have hex_r : ∃ cr : Fin 7, cr ≠ cv ∧ cr ≠ cq ∧ cr ≠ cu ∧ (cu = cv → cr ∉ Ey ∧ cr ∉ Ez) := by
      by_cases huv : cu = cv
      · rcases exists_color_not_mem (insert cv (insert cq (Ey ∪ Ez)))
            (card_insert2_union2 Ey Ez cv cq hEy hEz) with ⟨cr, hcr⟩
        simp only [Finset.mem_insert, Finset.mem_union, not_or] at hcr
        rcases hcr with ⟨hcr_cv, hcr_cq, hcr_Ey, hcr_Ez⟩
        exact ⟨cr, hcr_cv, hcr_cq, fun h => hcr_cv (h.trans huv), fun _ => ⟨hcr_Ey, hcr_Ez⟩⟩
      · rcases exists_color_not_mem {cv, cq, cu} (card_triple_lt cv cq cu) with ⟨cr, hcr⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcr
        rcases hcr with ⟨hcr_cv, hcr_cq, hcr_cu⟩
        exact ⟨cr, hcr_cv, hcr_cq, hcr_cu, fun h => absurd h huv⟩
    rcases hex_p with ⟨cp, hcp_cs, hcp_cq, hcp_ct, hcp_st⟩
    rcases hex_r with ⟨cr, hcr_cv, hcr_cq, hcr_cu, hcr_uv⟩
    exact ⟨cq, cp, cr, hcq_ct, hcq_cu, hcq_Ex, hcq_Ey,
      hcp_cs, hcp_cq, hcp_ct, hcr_cv, hcr_cq, hcr_cu,
      hcp_st, hcr_uv,
      fun h => absurd h hsq, fun h => absurd h hvq⟩

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
    simp only [SimpleGraph.EdgeLabeling.get, c, dif_pos rfl]
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

private lemma sym2_pair_ne {V : Type u} {u₁ v₁ u₂ v₂ : V}
    (h1 : u₁ ≠ u₂) (h2 : u₁ ≠ v₂) : s(u₁, v₁) ≠ s(u₂, v₂) := by
  intro heq
  rw [Sym2.eq_iff] at heq
  rcases heq with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact h1 rfl
  · exact h2 rfl

/-- Greedy insertion of the four pendant edges `s, t, u, v` into `G - {p, q, r}`,
returning an abstract `EdgeColoring` on `G - {p, q, r}` so subsequent proofs never unfold it. -/
private lemma build_G3_coloring {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hsub : IsSubcubic G) (w x y z w' x' y' z' : V)
    (hw_x : w ≠ x) (hw_y : w ≠ y) (hw_z : w ≠ z)
    (hw_x' : w ≠ x') (hw_y' : w ≠ y') (hw_z' : w ≠ z')
    (hx_y : x ≠ y) (hx_z : x ≠ z) (hx_y' : x ≠ y') (hx_z' : x ≠ z')
    (hy_z : y ≠ z) (hy_z' : y ≠ z')
    (hww'_G₃ : (G.deleteEdges {s(w, x), s(x, y), s(y, z)}).Adj w w')
    (hxx'_G₃ : (G.deleteEdges {s(w, x), s(x, y), s(y, z)}).Adj x x')
    (hyy'_G₃ : (G.deleteEdges {s(w, x), s(x, y), s(y, z)}).Adj y y')
    (hzz'_G₃ : (G.deleteEdges {s(w, x), s(x, y), s(y, z)}).Adj z z')
    (hw_only : ∀ a : V, (G.deleteEdges {s(w, x), s(x, y), s(y, z)}).Adj w a → a = w')
    (hx_only : ∀ a : V, (G.deleteEdges {s(w, x), s(x, y), s(y, z)}).Adj x a → a = x')
    (hy_only : ∀ a : V, (G.deleteEdges {s(w, x), s(x, y), s(y, z)}).Adj y a → a = y')
    (hz_only : ∀ a : V, (G.deleteEdges {s(w, x), s(x, y), s(y, z)}).Adj z a → a = z')
    (hc_init : HasStarEdgeColoring
      (G.deleteEdges {s(w, x), s(x, y), s(y, z), s(w, w'), s(x, x'), s(y, y'), s(z, z')}) 7) :
    ∃ c₃ : EdgeColoring (G.deleteEdges {s(w, x), s(x, y), s(y, z)}) (Fin 7),
      IsStarEdgeColoring c₃ ∧
      (∀ {a b : V},
        (G.deleteEdges {s(w, x), s(x, y), s(y, z), s(w, w'), s(x, x'), s(y, y'), s(z, z')}).Adj w' a →
        (hab : (G.deleteEdges {s(w, x), s(x, y), s(y, z), s(w, w'), s(x, x'), s(y, y'), s(z, z')}).Adj a b) →
        (hab₃ : (G.deleteEdges {s(w, x), s(x, y), s(y, z)}).Adj a b) →
        c₃.get a b hab₃ ≠ c₃.get w w' hww'_G₃) ∧
      (∀ {a b : V},
        (G.deleteEdges {s(w, x), s(x, y), s(y, z), s(w, w'), s(x, x'), s(y, y'), s(z, z')}).Adj x' a →
        (hab : (G.deleteEdges {s(w, x), s(x, y), s(y, z), s(w, w'), s(x, x'), s(y, y'), s(z, z')}).Adj a b) →
        (hab₃ : (G.deleteEdges {s(w, x), s(x, y), s(y, z)}).Adj a b) →
        c₃.get a b hab₃ ≠ c₃.get x x' hxx'_G₃) ∧
      (∀ {a b : V},
        (G.deleteEdges {s(w, x), s(x, y), s(y, z), s(w, w'), s(x, x'), s(y, y'), s(z, z')}).Adj y' a →
        (hab : (G.deleteEdges {s(w, x), s(x, y), s(y, z), s(w, w'), s(x, x'), s(y, y'), s(z, z')}).Adj a b) →
        (hab₃ : (G.deleteEdges {s(w, x), s(x, y), s(y, z)}).Adj a b) →
        c₃.get a b hab₃ ≠ c₃.get y y' hyy'_G₃) ∧
      (∀ {a b : V},
        (G.deleteEdges {s(w, x), s(x, y), s(y, z), s(w, w'), s(x, x'), s(y, y'), s(z, z')}).Adj z' a →
        (hab : (G.deleteEdges {s(w, x), s(x, y), s(y, z), s(w, w'), s(x, x'), s(y, y'), s(z, z')}).Adj a b) →
        (hab₃ : (G.deleteEdges {s(w, x), s(x, y), s(y, z)}).Adj a b) →
        c₃.get a b hab₃ ≠ c₃.get z z' hzz'_G₃) ∧
      ((G.deleteEdges {s(w, x), s(x, y), s(y, z), s(w, w'), s(x, x'), s(y, y'), s(z, z')}).Adj w' x' →
        c₃.get w w' hww'_G₃ ≠ c₃.get x x' hxx'_G₃) ∧
      ((G.deleteEdges {s(w, x), s(x, y), s(y, z), s(w, w'), s(x, x'), s(y, y'), s(z, z')}).Adj w' y' →
        c₃.get w w' hww'_G₃ ≠ c₃.get y y' hyy'_G₃) ∧
      ((G.deleteEdges {s(w, x), s(x, y), s(y, z), s(w, w'), s(x, x'), s(y, y'), s(z, z')}).Adj x' y' →
        c₃.get x x' hxx'_G₃ ≠ c₃.get y y' hyy'_G₃) ∧
      ((G.deleteEdges {s(w, x), s(x, y), s(y, z), s(w, w'), s(x, x'), s(y, y'), s(z, z')}).Adj w' z' →
        c₃.get w w' hww'_G₃ ≠ c₃.get z z' hzz'_G₃) ∧
      ((G.deleteEdges {s(w, x), s(x, y), s(y, z), s(w, w'), s(x, x'), s(y, y'), s(z, z')}).Adj x' z' →
        c₃.get x x' hxx'_G₃ ≠ c₃.get z z' hzz'_G₃) ∧
      ((G.deleteEdges {s(w, x), s(x, y), s(y, z), s(w, w'), s(x, x'), s(y, y'), s(z, z')}).Adj y' z' →
        c₃.get y y' hyy'_G₃ ≠ c₃.get z z' hzz'_G₃) := by
  classical
  let G_init := G.deleteEdges {s(w, x), s(x, y), s(y, z), s(w, w'), s(x, x'), s(y, y'), s(z, z')}
  let G₃ := G.deleteEdges {s(w, x), s(x, y), s(y, z)}
  let H₃ := G₃.deleteEdges {s(z, z')}
  let H₂ := H₃.deleteEdges {s(y, y')}
  let H₁ := H₂.deleteEdges {s(x, x')}
  let H₀ := H₁.deleteEdges {s(w, w')}

  have hG₃_le : G₃ ≤ G := SimpleGraph.deleteEdges_le _
  have hH₃_le : H₃ ≤ G₃ := SimpleGraph.deleteEdges_le _
  have hH₂_le : H₂ ≤ H₃ := SimpleGraph.deleteEdges_le _
  have hH₁_le : H₁ ≤ H₂ := SimpleGraph.deleteEdges_le _
  have hH₀_le : H₀ ≤ H₁ := SimpleGraph.deleteEdges_le _

  have hH₀_le_init : H₀ ≤ G_init := by
    intro a b hab
    rcases SimpleGraph.deleteEdges_adj.mp hab with ⟨hab1, nw⟩
    rcases SimpleGraph.deleteEdges_adj.mp hab1 with ⟨hab2, nx⟩
    rcases SimpleGraph.deleteEdges_adj.mp hab2 with ⟨hab3, ny⟩
    rcases SimpleGraph.deleteEdges_adj.mp hab3 with ⟨habG₃, nz⟩
    rcases SimpleGraph.deleteEdges_adj.mp habG₃ with ⟨habG, npqr⟩
    rw [Set.mem_singleton_iff] at nw nx ny nz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at npqr
    refine SimpleGraph.deleteEdges_adj.mpr ⟨habG, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨npqr.1, npqr.2.1, npqr.2.2, nw, nx, ny, nz⟩

  have hinit_le_H₀ : G_init ≤ H₀ := by
    intro a b hab
    rcases SimpleGraph.deleteEdges_adj.mp hab with ⟨habG, n7⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at n7
    rcases n7 with ⟨nwx, nxy, nyz, nw, nx, ny, nz⟩
    have g3 : G₃.Adj a b := SimpleGraph.deleteEdges_adj.mpr ⟨habG, by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]; exact ⟨nwx, nxy, nyz⟩⟩
    have h3 : H₃.Adj a b := SimpleGraph.deleteEdges_adj.mpr ⟨g3, nz⟩
    have h2 : H₂.Adj a b := SimpleGraph.deleteEdges_adj.mpr ⟨h3, ny⟩
    have h1 : H₁.Adj a b := SimpleGraph.deleteEdges_adj.mpr ⟨h2, nx⟩
    exact SimpleGraph.deleteEdges_adj.mpr ⟨h1, nw⟩

  rcases hc_init with ⟨c_init, hc_init_star⟩
  let c₀ : EdgeColoring H₀ (Fin 7) := restrictColoring hH₀_le_init c_init
  have hc₀ : IsStarEdgeColoring c₀ := isStarEdgeColoring_mono hH₀_le_init hc_init_star

  have hsub_G₃ : IsSubcubic G₃ :=
    fun v => le_trans (Set.encard_le_encard (SimpleGraph.neighborSet_mono hG₃_le v)) (hsub v)
  have hsub_H₃ : IsSubcubic H₃ :=
    fun v => le_trans (Set.encard_le_encard (SimpleGraph.neighborSet_mono hH₃_le v)) (hsub_G₃ v)
  have hsub_H₂ : IsSubcubic H₂ :=
    fun v => le_trans (Set.encard_le_encard (SimpleGraph.neighborSet_mono hH₂_le v)) (hsub_H₃ v)
  have hsub_H₁ : IsSubcubic H₁ :=
    fun v => le_trans (Set.encard_le_encard (SimpleGraph.neighborSet_mono hH₁_le v)) (hsub_H₂ v)

  have hww'_H₃ : H₃.Adj w w' := SimpleGraph.deleteEdges_adj.mpr ⟨hww'_G₃, sym2_pair_ne hw_z hw_z'⟩
  have hww'_H₂ : H₂.Adj w w' := SimpleGraph.deleteEdges_adj.mpr ⟨hww'_H₃, sym2_pair_ne hw_y hw_y'⟩
  have hww'_H₁ : H₁.Adj w w' := SimpleGraph.deleteEdges_adj.mpr ⟨hww'_H₂, sym2_pair_ne hw_x hw_x'⟩
  have hxx'_H₃ : H₃.Adj x x' := SimpleGraph.deleteEdges_adj.mpr ⟨hxx'_G₃, sym2_pair_ne hx_z hx_z'⟩
  have hxx'_H₂ : H₂.Adj x x' := SimpleGraph.deleteEdges_adj.mpr ⟨hxx'_H₃, sym2_pair_ne hx_y hx_y'⟩
  have hyy'_H₃ : H₃.Adj y y' := SimpleGraph.deleteEdges_adj.mpr ⟨hyy'_G₃, sym2_pair_ne hy_z hy_z'⟩

  rcases extend_pendant_seven hsub_H₁ w w' hww'_H₁
      (fun a ha => hw_only a (hH₃_le (hH₂_le (hH₁_le ha)))) c₀ hc₀ with
    ⟨c₁, hc₁, hc₁_ag, hc₁_av⟩
  rcases extend_pendant_seven hsub_H₂ x x' hxx'_H₂
      (fun a ha => hx_only a (hH₃_le (hH₂_le ha))) c₁ hc₁ with
    ⟨c₂, hc₂, hc₂_ag, hc₂_av⟩
  rcases extend_pendant_seven hsub_H₃ y y' hyy'_H₃
      (fun a ha => hy_only a (hH₃_le ha)) c₂ hc₂ with
    ⟨c₃_pre, hc₃_pre, hc₃_pre_ag, hc₃_pre_av⟩
  rcases extend_pendant_seven hsub_G₃ z z' hzz'_G₃
      hz_only c₃_pre hc₃_pre with
    ⟨c₃, hc₃, hc₃_ag, hc₃_av⟩

  have eq_c₃_H₃ : ∀ {a b : V} (h : H₃.Adj a b), c₃.get a b (hH₃_le h) = c₃_pre.get a b h :=
    fun h => hc₃_ag _ _ h
  have eq_c₃_H₂ : ∀ {a b : V} (h : H₂.Adj a b), c₃.get a b (hH₃_le (hH₂_le h)) = c₂.get a b h :=
    fun h => (eq_c₃_H₃ (hH₂_le h)).trans (hc₃_pre_ag _ _ h)
  have eq_c₃_H₁ : ∀ {a b : V} (h : H₁.Adj a b), c₃.get a b (hH₃_le (hH₂_le (hH₁_le h))) = c₁.get a b h :=
    fun h => (eq_c₃_H₂ (hH₁_le h)).trans (hc₂_ag _ _ h)

  refine ⟨c₃, hc₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hua hab hab₃
    have hab0 := hinit_le_H₀ hab
    rw [c_get_eq_of_sym2 c₃ hab₃ (hH₃_le (hH₂_le (hH₁_le (hH₀_le hab0)))) rfl,
      eq_c₃_H₁ (hH₀_le hab0), eq_c₃_H₁ hww'_H₁]
    exact hc₁_av a b hab0 (hinit_le_H₀ hua)
  · intro a b hua hab hab₃
    have hab0 := hinit_le_H₀ hab
    rw [c_get_eq_of_sym2 c₃ hab₃ (hH₃_le (hH₂_le (hH₁_le (hH₀_le hab0)))) rfl,
      eq_c₃_H₂ (hH₁_le (hH₀_le hab0)), eq_c₃_H₂ hxx'_H₂]
    exact hc₂_av a b (hH₀_le hab0) (hH₀_le (hinit_le_H₀ hua))
  · intro a b hua hab hab₃
    have hab0 := hinit_le_H₀ hab
    rw [c_get_eq_of_sym2 c₃ hab₃ (hH₃_le (hH₂_le (hH₁_le (hH₀_le hab0)))) rfl,
      eq_c₃_H₃ (hH₂_le (hH₁_le (hH₀_le hab0))), eq_c₃_H₃ hyy'_H₃]
    exact hc₃_pre_av a b (hH₁_le (hH₀_le hab0)) (hH₁_le (hH₀_le (hinit_le_H₀ hua)))
  · intro a b hua hab hab₃
    have hab0 := hinit_le_H₀ hab
    rw [c_get_eq_of_sym2 c₃ hab₃ (hH₃_le (hH₂_le (hH₁_le (hH₀_le hab0)))) rfl]
    exact hc₃_av a b (hH₂_le (hH₁_le (hH₀_le hab0))) (hH₂_le (hH₁_le (hH₀_le (hinit_le_H₀ hua))))
  · intro h0
    have h := hc₂_av w' w hww'_H₁.symm (hH₀_le (hinit_le_H₀ h0).symm)
    rw [← eq_c₃_H₂ (hH₁_le hww'_H₁.symm), ← eq_c₃_H₂ hxx'_H₂, c_get_symm c₃ hww'_G₃] at h
    exact h
  · intro h0
    have h := hc₃_pre_av w' w (hH₁_le hww'_H₁.symm) (hH₁_le (hH₀_le (hinit_le_H₀ h0).symm))
    rw [← eq_c₃_H₃ (hH₂_le (hH₁_le hww'_H₁.symm)), ← eq_c₃_H₃ hyy'_H₃, c_get_symm c₃ hww'_G₃] at h
    exact h
  · intro h0
    have h := hc₃_pre_av x' x hxx'_H₂.symm (hH₁_le (hH₀_le (hinit_le_H₀ h0).symm))
    rw [← eq_c₃_H₃ (hH₂_le hxx'_H₂.symm), ← eq_c₃_H₃ hyy'_H₃, c_get_symm c₃ hxx'_G₃] at h
    exact h
  · intro h0
    have h := hc₃_av w' w (hH₂_le (hH₁_le hww'_H₁.symm)) (hH₂_le (hH₁_le (hH₀_le (hinit_le_H₀ h0).symm)))
    rw [c_get_symm c₃ hww'_G₃] at h
    exact h
  · intro h0
    have h := hc₃_av x' x (hH₂_le hxx'_H₂.symm) (hH₂_le (hH₁_le (hH₀_le (hinit_le_H₀ h0).symm)))
    rw [c_get_symm c₃ hxx'_G₃] at h
    exact h
  · intro h0
    have h := hc₃_av y' y hyy'_H₃.symm (hH₂_le (hH₁_le (hH₀_le (hinit_le_H₀ h0).symm)))
    rw [c_get_symm c₃ hyy'_G₃] at h
    exact h

/-- Abstract constructor for the final coloring `c` on `G`, keeping `c` opaque in the main proof. -/
private lemma build_G_coloring {V : Type u} {G : SimpleGraph V}
    (w x y z : V) (hw_y : w ≠ y) (hw_z : w ≠ z) (hx_y : x ≠ y) (hx_z : x ≠ z)
    (hwx : G.Adj w x) (hxy : G.Adj x y) (hyz : G.Adj y z)
    (c₃ : EdgeColoring (G.deleteEdges {s(w, x), s(x, y), s(y, z)}) (Fin 7))
    (cq cp cr : Fin 7) :
    ∃ c : EdgeColoring G (Fin 7),
      c.get w x hwx = cp ∧
      c.get x y hxy = cq ∧
      c.get y z hyz = cr ∧
      (∀ {a b : V} (hab₃ : (G.deleteEdges {s(w, x), s(x, y), s(y, z)}).Adj a b),
        c.get a b (SimpleGraph.deleteEdges_le {s(w, x), s(x, y), s(y, z)} hab₃) = c₃.get a b hab₃) := by
  classical
  let c : EdgeColoring G (Fin 7) := fun e =>
    if h1 : e.1 = s(w, x) then cp
    else if h2 : e.1 = s(x, y) then cq
    else if h3 : e.1 = s(y, z) then cr
    else c₃ ⟨e.1, by
      rcases e with ⟨⟨a, b⟩, hab⟩
      refine SimpleGraph.deleteEdges_adj.mpr ⟨hab, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨h1, h2, h3⟩⟩
  have hne_wx_xy : s(w, x) ≠ s(x, y) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact hx_y h2
    · exact hw_y h1
  have hne_wx_yz : s(w, x) ≠ s(y, z) := sym2_pair_ne hw_y hw_z
  have hne_xy_yz : s(x, y) ≠ s(y, z) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hx_y h1
    · exact hx_z h1
  refine ⟨c, ?_, ?_, ?_, ?_⟩
  · simp only [SimpleGraph.EdgeLabeling.get, c, dite_true]
  · simp only [SimpleGraph.EdgeLabeling.get, c, dif_neg hne_wx_xy.symm, dite_true]
  · simp only [SimpleGraph.EdgeLabeling.get, c, dif_neg hne_wx_yz.symm, dif_neg hne_xy_yz.symm, dite_true]
  · intro a b hab₃
    have hnot := (SimpleGraph.deleteEdges_adj.mp hab₃).2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hnot
    rcases hnot with ⟨h1, h2, h3⟩
    simp only [SimpleGraph.EdgeLabeling.get, c, dif_neg h1, dif_neg h2, dif_neg h3]

/-- Dvořák–Mohar–Šámal (2013) path-of-four configuration reduction:
if `w - x - y - z` is a path in a subcubic graph `G` where `w` and `z` have degree at most `2`
and `w, x, y, z` together with their other neighbors `w', x', y', z'` are `8` distinct vertices,
then any star `7`-edge-coloring of `G` minus the `7` edges incident to `{w, x, y, z}` extends
to a star `7`-edge-coloring of `G`. -/
private theorem hasStarEdgeColoring_of_deg2_path4_distinct {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hsub : IsSubcubic G) (w x y z w' x' y' z' : V)
    (hnd : [w, x, y, z, w', x', y', z'].Nodup)
    (hwx : G.Adj w x) (hxy : G.Adj x y) (hyz : G.Adj y z)
    (hww' : G.Adj w w') (hxx' : G.Adj x x') (hyy' : G.Adj y y') (hzz' : G.Adj z z')
    (hw2 : (G.neighborSet w).encard ≤ 2) (hz2 : (G.neighborSet z).encard ≤ 2)
    (hc' : HasStarEdgeColoring
      (G.deleteEdges {s(w, x), s(x, y), s(y, z), s(w, w'), s(x, x'), s(y, y'), s(z, z')}) 7) :
    HasStarEdgeColoring G 7 := by
  classical
  have hnd0 := hnd
  rw [List.nodup_cons] at hnd0; rcases hnd0 with ⟨m_w, hnd1⟩
  rw [List.nodup_cons] at hnd1; rcases hnd1 with ⟨m_x, hnd2⟩
  rw [List.nodup_cons] at hnd2; rcases hnd2 with ⟨m_y, hnd3⟩
  rw [List.nodup_cons] at hnd3; rcases hnd3 with ⟨m_z, hnd4'⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at m_w m_x m_y m_z
  rcases m_w with ⟨hw_x, hw_y, hw_z, hw_w', hw_x', hw_y', hw_z'⟩
  rcases m_x with ⟨hx_y, hx_z, hx_w', hx_x', hx_y', hx_z'⟩
  rcases m_y with ⟨hy_z, hy_w', hy_x', hy_y', hy_z'⟩
  rcases m_z with ⟨hz_w', hz_x', hz_y', hz_z'⟩
  rcases nodup4_elim hnd4' with ⟨hw'_x', hw'_y', hw'_z', hx'_y', hx'_z', hy'_z'⟩
  change w ≠ x at hw_x; change w ≠ y at hw_y; change w ≠ z at hw_z
  change w ≠ w' at hw_w'; change w ≠ x' at hw_x'; change w ≠ y' at hw_y'; change w ≠ z' at hw_z'
  change x ≠ y at hx_y; change x ≠ z at hx_z
  change x ≠ w' at hx_w'; change x ≠ x' at hx_x'; change x ≠ y' at hx_y'; change x ≠ z' at hx_z'
  change y ≠ z at hy_z
  change y ≠ w' at hy_w'; change y ≠ x' at hy_x'; change y ≠ y' at hy_y'; change y ≠ z' at hy_z'
  change z ≠ w' at hz_w'; change z ≠ x' at hz_x'; change z ≠ y' at hz_y'; change z ≠ z' at hz_z'

  have adj_w : ∀ u : V, G.Adj w u ↔ u = x ∨ u = w' :=
    neighbor_eq_pair hx_w' hwx hww' hw2
  have adj_x : ∀ u : V, G.Adj x u ↔ u = w ∨ u = y ∨ u = x' :=
    neighbor_eq_triple hw_y hw_x' hy_x' hwx.symm hxy hxx' hsub
  have adj_y : ∀ u : V, G.Adj y u ↔ u = x ∨ u = z ∨ u = y' :=
    neighbor_eq_triple hx_z hx_y' hz_y' hxy.symm hyz hyy' hsub
  have adj_z : ∀ u : V, G.Adj z u ↔ u = y ∨ u = z' :=
    neighbor_eq_pair hy_z' hyz.symm hzz' hz2

  let A : V → Prop := fun v => v = w ∨ v = x ∨ v = y ∨ v = z
  have hnA_w' : ¬ A w' := by
    rintro (h | h | h | h); exact hw_w' h.symm; exact hx_w' h.symm; exact hy_w' h.symm; exact hz_w' h.symm
  have hnA_x' : ¬ A x' := by
    rintro (h | h | h | h); exact hw_x' h.symm; exact hx_x' h.symm; exact hy_x' h.symm; exact hz_x' h.symm
  have hnA_y' : ¬ A y' := by
    rintro (h | h | h | h); exact hw_y' h.symm; exact hx_y' h.symm; exact hy_y' h.symm; exact hz_y' h.symm
  have hnA_z' : ¬ A z' := by
    rintro (h | h | h | h); exact hw_z' h.symm; exact hx_z' h.symm; exact hy_z' h.symm; exact hz_z' h.symm

  have adj_A_notA : ∀ {u v : V}, A u → ¬ A v → G.Adj u v →
      (u = w ∧ v = w') ∨ (u = x ∧ v = x') ∨ (u = y ∧ v = y') ∨ (u = z ∧ v = z') := by
    intro u v hu hv huv
    rcases hu with rfl | rfl | rfl | rfl
    · rcases (adj_w v).mp huv with rfl | rfl
      · exact absurd (Or.inr (Or.inl rfl)) hv
      · exact Or.inl ⟨rfl, rfl⟩
    · rcases (adj_x v).mp huv with rfl | rfl | rfl
      · exact absurd (Or.inl rfl) hv
      · exact absurd (Or.inr (Or.inr (Or.inl rfl))) hv
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · rcases (adj_y v).mp huv with rfl | rfl | rfl
      · exact absurd (Or.inr (Or.inl rfl)) hv
      · exact absurd (Or.inr (Or.inr (Or.inr rfl))) hv
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · rcases (adj_z v).mp huv with rfl | rfl
      · exact absurd (Or.inr (Or.inr (Or.inl rfl))) hv
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))

  have adj_A_A : ∀ {u v : V}, A u → A v → G.Adj u v →
      (u = w ∧ v = x) ∨ (u = x ∧ v = w) ∨ (u = x ∧ v = y) ∨
      (u = y ∧ v = x) ∨ (u = y ∧ v = z) ∨ (u = z ∧ v = y) := by
    intro u v hu hv huv
    rcases hu with rfl | rfl | rfl | rfl
    · rcases (adj_w v).mp huv with rfl | rfl
      · exact Or.inl ⟨rfl, rfl⟩
      · exact absurd hv hnA_w'
    · rcases (adj_x v).mp huv with rfl | rfl | rfl
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
      · exact absurd hv hnA_x'
    · rcases (adj_y v).mp huv with rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
      · exact absurd hv hnA_y'
    · rcases (adj_z v).mp huv with rfl | rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
      · exact absurd hv hnA_z'

  have path2_A : ∀ {u₁ u₂ u₃ : V}, A u₁ → A u₂ → A u₃ → u₁ ≠ u₃ →
      G.Adj u₁ u₂ → G.Adj u₂ u₃ →
      (u₁ = w ∧ u₂ = x ∧ u₃ = y) ∨ (u₁ = y ∧ u₂ = x ∧ u₃ = w) ∨
      (u₁ = x ∧ u₂ = y ∧ u₃ = z) ∨ (u₁ = z ∧ u₂ = y ∧ u₃ = x) := by
    intro u₁ u₂ u₃ h1 h2 h3 hne13 h12 h23
    rcases adj_A_A h1 h2 h12 with ⟨hu1, hu2⟩ | ⟨hu1, hu2⟩ | ⟨hu1, hu2⟩ |
        ⟨hu1, hu2⟩ | ⟨hu1, hu2⟩ | ⟨hu1, hu2⟩
    · rcases adj_A_A h2 h3 h23 with ⟨h, _⟩ | ⟨_, hu3⟩ | ⟨_, hu3⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · exact absurd (hu2.symm.trans h).symm hw_x
      · exact absurd (hu1.trans hu3.symm) hne13
      · exact Or.inl ⟨hu1, hu2, hu3⟩
      · exact absurd (hu2.symm.trans h) hx_y
      · exact absurd (hu2.symm.trans h) hx_y
      · exact absurd (hu2.symm.trans h) hx_z
    · rcases adj_A_A h2 h3 h23 with ⟨_, hu3⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · exact absurd (hu1.trans hu3.symm) hne13
      · exact absurd (hu2.symm.trans h) hw_x
      · exact absurd (hu2.symm.trans h) hw_x
      · exact absurd (hu2.symm.trans h) hw_y
      · exact absurd (hu2.symm.trans h) hw_y
      · exact absurd (hu2.symm.trans h) hw_z
    · rcases adj_A_A h2 h3 h23 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, hu3⟩ | ⟨_, hu3⟩ | ⟨h, _⟩
      · exact absurd (hu2.symm.trans h).symm hw_y
      · exact absurd (hu2.symm.trans h).symm hx_y
      · exact absurd (hu2.symm.trans h).symm hx_y
      · exact absurd (hu1.trans hu3.symm) hne13
      · exact Or.inr (Or.inr (Or.inl ⟨hu1, hu2, hu3⟩))
      · exact absurd (hu2.symm.trans h) hy_z
    · rcases adj_A_A h2 h3 h23 with ⟨h, _⟩ | ⟨_, hu3⟩ | ⟨_, hu3⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · exact absurd (hu2.symm.trans h).symm hw_x
      · exact Or.inr (Or.inl ⟨hu1, hu2, hu3⟩)
      · exact absurd (hu1.trans hu3.symm) hne13
      · exact absurd (hu2.symm.trans h) hx_y
      · exact absurd (hu2.symm.trans h) hx_y
      · exact absurd (hu2.symm.trans h) hx_z
    · rcases adj_A_A h2 h3 h23 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, hu3⟩
      · exact absurd (hu2.symm.trans h).symm hw_z
      · exact absurd (hu2.symm.trans h).symm hx_z
      · exact absurd (hu2.symm.trans h).symm hx_z
      · exact absurd (hu2.symm.trans h).symm hy_z
      · exact absurd (hu2.symm.trans h).symm hy_z
      · exact absurd (hu1.trans hu3.symm) hne13
    · rcases adj_A_A h2 h3 h23 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, hu3⟩ | ⟨_, hu3⟩ | ⟨h, _⟩
      · exact absurd (hu2.symm.trans h).symm hw_y
      · exact absurd (hu2.symm.trans h).symm hx_y
      · exact absurd (hu2.symm.trans h).symm hx_y
      · exact Or.inr (Or.inr (Or.inr ⟨hu1, hu2, hu3⟩))
      · exact absurd (hu1.trans hu3.symm) hne13
      · exact absurd (hu2.symm.trans h) hy_z

  have path3_A : ∀ {u₁ u₂ u₃ u₄ : V}, A u₁ → A u₂ → A u₃ → A u₄ →
      [u₁, u₂, u₃, u₄].Nodup → G.Adj u₁ u₂ → G.Adj u₂ u₃ → G.Adj u₃ u₄ →
      (u₁ = w ∧ u₂ = x ∧ u₃ = y ∧ u₄ = z) ∨ (u₁ = z ∧ u₂ = y ∧ u₃ = x ∧ u₄ = w) := by
    intro u₁ u₂ u₃ u₄ h1 h2 h3 h4 hnd4 h12 h23 h34
    rcases nodup4_elim hnd4 with ⟨_, n13, _, _, n24, _⟩
    rcases path2_A h1 h2 h3 n13 h12 h23 with
        ⟨hu1, hu2, hu3⟩ | ⟨hu1, hu2, hu3⟩ | ⟨hu1, hu2, hu3⟩ | ⟨hu1, hu2, hu3⟩
    · rcases adj_A_A h3 h4 h34 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, hu4⟩ | ⟨_, hu4⟩ | ⟨h, _⟩
      · exact absurd (hu3.symm.trans h).symm hw_y
      · exact absurd (hu3.symm.trans h).symm hx_y
      · exact absurd (hu3.symm.trans h).symm hx_y
      · exact absurd (hu2.trans hu4.symm) n24
      · exact Or.inl ⟨hu1, hu2, hu3, hu4⟩
      · exact absurd (hu3.symm.trans h) hy_z
    · rcases adj_A_A h3 h4 h34 with ⟨_, hu4⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · exact absurd (hu2.trans hu4.symm) n24
      · exact absurd (hu3.symm.trans h) hw_x
      · exact absurd (hu3.symm.trans h) hw_x
      · exact absurd (hu3.symm.trans h) hw_y
      · exact absurd (hu3.symm.trans h) hw_y
      · exact absurd (hu3.symm.trans h) hw_z
    · rcases adj_A_A h3 h4 h34 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, hu4⟩
      · exact absurd (hu3.symm.trans h).symm hw_z
      · exact absurd (hu3.symm.trans h).symm hx_z
      · exact absurd (hu3.symm.trans h).symm hx_z
      · exact absurd (hu3.symm.trans h).symm hy_z
      · exact absurd (hu3.symm.trans h).symm hy_z
      · exact absurd (hu2.trans hu4.symm) n24
    · rcases adj_A_A h3 h4 h34 with ⟨h, _⟩ | ⟨_, hu4⟩ | ⟨_, hu4⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · exact absurd (hu3.symm.trans h).symm hw_x
      · exact Or.inr ⟨hu1, hu2, hu3, hu4⟩
      · exact absurd (hu2.trans hu4.symm) n24
      · exact absurd (hu3.symm.trans h) hx_y
      · exact absurd (hu3.symm.trans h) hx_y
      · exact absurd (hu3.symm.trans h) hx_z

  have not_pqr_of_notA : ∀ {a b : V}, (¬ A a ∨ ¬ A b) →
      s(a, b) ∉ ({s(w, x), s(x, y), s(y, z)} : Set (Sym2 V)) := by
    intro a b hna hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.eq_iff] at hmem
    rcases hna with ha | hb
    · rcases hmem with (⟨rfl, _⟩ | ⟨rfl, _⟩) | (⟨rfl, _⟩ | ⟨rfl, _⟩) | (⟨rfl, _⟩ | ⟨rfl, _⟩)
      · exact ha (Or.inl rfl)
      · exact ha (Or.inr (Or.inl rfl))
      · exact ha (Or.inr (Or.inl rfl))
      · exact ha (Or.inr (Or.inr (Or.inl rfl)))
      · exact ha (Or.inr (Or.inr (Or.inl rfl)))
      · exact ha (Or.inr (Or.inr (Or.inr rfl)))
    · rcases hmem with (⟨_, rfl⟩ | ⟨_, rfl⟩) | (⟨_, rfl⟩ | ⟨_, rfl⟩) | (⟨_, rfl⟩ | ⟨_, rfl⟩)
      · exact hb (Or.inr (Or.inl rfl))
      · exact hb (Or.inl rfl)
      · exact hb (Or.inr (Or.inr (Or.inl rfl)))
      · exact hb (Or.inr (Or.inl rfl))
      · exact hb (Or.inr (Or.inr (Or.inr rfl)))
      · exact hb (Or.inr (Or.inr (Or.inl rfl)))

  have adj_G₃_of_notA : ∀ {a b : V}, G.Adj a b → (¬ A a ∨ ¬ A b) →
      (G.deleteEdges {s(w, x), s(x, y), s(y, z)}).Adj a b :=
    fun hab hna => SimpleGraph.deleteEdges_adj.mpr ⟨hab, not_pqr_of_notA hna⟩

  have adj_init_of_notA2 : ∀ {a b : V}, G.Adj a b → ¬ A a → ¬ A b →
      (G.deleteEdges {s(w, x), s(x, y), s(y, z), s(w, w'), s(x, x'), s(y, y'), s(z, z')}).Adj a b := by
    intro a b hab ha hb
    refine SimpleGraph.deleteEdges_adj.mpr ⟨hab, ?_⟩
    intro hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.eq_iff] at hmem
    rcases hmem with (⟨rfl, _⟩ | ⟨_, rfl⟩) | (⟨rfl, _⟩ | ⟨_, rfl⟩) | (⟨rfl, _⟩ | ⟨_, rfl⟩) |
        (⟨rfl, _⟩ | ⟨_, rfl⟩) | (⟨rfl, _⟩ | ⟨_, rfl⟩) | (⟨rfl, _⟩ | ⟨_, rfl⟩) | (⟨rfl, _⟩ | ⟨_, rfl⟩)
    · exact ha (Or.inl rfl)
    · exact hb (Or.inl rfl)
    · exact ha (Or.inr (Or.inl rfl))
    · exact hb (Or.inr (Or.inl rfl))
    · exact ha (Or.inr (Or.inr (Or.inl rfl)))
    · exact hb (Or.inr (Or.inr (Or.inl rfl)))
    · exact ha (Or.inl rfl)
    · exact hb (Or.inl rfl)
    · exact ha (Or.inr (Or.inl rfl))
    · exact hb (Or.inr (Or.inl rfl))
    · exact ha (Or.inr (Or.inr (Or.inl rfl)))
    · exact hb (Or.inr (Or.inr (Or.inl rfl)))
    · exact ha (Or.inr (Or.inr (Or.inr rfl)))
    · exact hb (Or.inr (Or.inr (Or.inr rfl)))

  have hww'_G₃ : (G.deleteEdges {s(w, x), s(x, y), s(y, z)}).Adj w w' := adj_G₃_of_notA hww' (Or.inr hnA_w')
  have hxx'_G₃ : (G.deleteEdges {s(w, x), s(x, y), s(y, z)}).Adj x x' := adj_G₃_of_notA hxx' (Or.inr hnA_x')
  have hyy'_G₃ : (G.deleteEdges {s(w, x), s(x, y), s(y, z)}).Adj y y' := adj_G₃_of_notA hyy' (Or.inr hnA_y')
  have hzz'_G₃ : (G.deleteEdges {s(w, x), s(x, y), s(y, z)}).Adj z z' := adj_G₃_of_notA hzz' (Or.inr hnA_z')

  have hw_only_G₃ : ∀ a : V, (G.deleteEdges {s(w, x), s(x, y), s(y, z)}).Adj w a → a = w' := by
    intro a hwa
    rcases SimpleGraph.deleteEdges_adj.mp hwa with ⟨hwaG, hne⟩
    rcases (adj_w a).mp hwaG with rfl | rfl
    · exact absurd (Set.mem_insert _ _) hne
    · rfl
  have hx_only_G₃ : ∀ a : V, (G.deleteEdges {s(w, x), s(x, y), s(y, z)}).Adj x a → a = x' := by
    intro a hxa
    rcases SimpleGraph.deleteEdges_adj.mp hxa with ⟨hxaG, hne⟩
    rcases (adj_x a).mp hxaG with rfl | rfl | rfl
    · exact absurd (by simp [Sym2.eq_swap]) hne
    · exact absurd (by simp) hne
    · rfl
  have hy_only_G₃ : ∀ a : V, (G.deleteEdges {s(w, x), s(x, y), s(y, z)}).Adj y a → a = y' := by
    intro a hya
    rcases SimpleGraph.deleteEdges_adj.mp hya with ⟨hyaG, hne⟩
    rcases (adj_y a).mp hyaG with rfl | rfl | rfl
    · exact absurd (by simp [Sym2.eq_swap]) hne
    · exact absurd (by simp) hne
    · rfl
  have hz_only_G₃ : ∀ a : V, (G.deleteEdges {s(w, x), s(x, y), s(y, z)}).Adj z a → a = z' := by
    intro a hza
    rcases SimpleGraph.deleteEdges_adj.mp hza with ⟨hzaG, hne⟩
    rcases (adj_z a).mp hzaG with rfl | rfl
    · exact absurd (by simp [Sym2.eq_swap]) hne
    · rfl

  rcases build_G3_coloring hsub w x y z w' x' y' z'
      hw_x hw_y hw_z hw_x' hw_y' hw_z' hx_y hx_z hx_y' hx_z' hy_z hy_z'
      hww'_G₃ hxx'_G₃ hyy'_G₃ hzz'_G₃
      hw_only_G₃ hx_only_G₃ hy_only_G₃ hz_only_G₃ hc' with
    ⟨c₃, hc₃, av_w, av_x, av_y, av_z, av_wx, av_wy, av_xy, av_wz, av_xz, av_yz⟩

  have hG₃_le : G.deleteEdges {s(w, x), s(x, y), s(y, z)} ≤ G := SimpleGraph.deleteEdges_le _

  let mkE (u u' : V) : Finset (Fin 7) :=
    (((G.deleteEdges {s(w, x), s(x, y), s(y, z)}).neighborFinset u').erase u).image fun a =>
      if ha : (G.deleteEdges {s(w, x), s(x, y), s(y, z)}).Adj u' a then c₃.get u' a ha else 0
  have card_mkE : ∀ {u u' : V}, G.Adj u u' → (mkE u u').card ≤ 2 := by
    intro u u' huu'
    have hsub_er : ((G.deleteEdges {s(w, x), s(x, y), s(y, z)}).neighborFinset u').erase u ⊆
        (G.neighborFinset u').erase u := by
      intro a ha
      rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset] at ha ⊢
      exact ⟨ha.1, hG₃_le ha.2⟩
    have h1 : (mkE u u').card ≤ (((G.deleteEdges {s(w, x), s(x, y), s(y, z)}).neighborFinset u').erase u).card :=
      Finset.card_image_le
    have h2 := Finset.card_le_card hsub_er
    rw [Finset.card_erase_of_mem ((SimpleGraph.mem_neighborFinset G u' u).mpr huu'.symm)] at h2
    have h3 := card_neighborFinset_le_three hsub u'
    omega

  have mem_mkE : ∀ {u u' a : V}, a ≠ u →
      (ha : (G.deleteEdges {s(w, x), s(x, y), s(y, z)}).Adj u' a) →
      c₃.get u' a ha ∈ mkE u u' := by
    intro u u' a hne ha
    refine Finset.mem_image.mpr ⟨a, Finset.mem_erase.mpr
      ⟨hne, (SimpleGraph.mem_neighborFinset _ u' a).mpr ha⟩, ?_⟩
    simp only [dif_pos ha]

  rcases exists_qpr_colors
      (c₃.get w w' hww'_G₃) (c₃.get x x' hxx'_G₃) (c₃.get y y' hyy'_G₃) (c₃.get z z' hzz'_G₃)
      (mkE w w') (mkE x x') (mkE y y') (mkE z z')
      (card_mkE hww') (card_mkE hxx') (card_mkE hyy') (card_mkE hzz') with
    ⟨cq, cp, cr,
      hcq_ct, hcq_cu, hcq_Ex, hcq_Ey,
      hcp_cs, hcp_cq, hcp_ct,
      hcr_cv, hcr_cq, hcr_cu,
      h_cs_ct, h_cu_cv, h_cs_cq, h_cv_cq⟩

  rcases build_G_coloring w x y z hw_y hw_z hx_y hx_z hwx hxy hyz c₃ cq cp cr with
    ⟨c, hc_wx, hc_xy, hc_yz, hc_G₃⟩

  have hc_ww' : c.get w w' hww' = c₃.get w w' hww'_G₃ := hc_G₃ hww'_G₃
  have hc_xx' : c.get x x' hxx' = c₃.get x x' hxx'_G₃ := hc_G₃ hxx'_G₃
  have hc_yy' : c.get y y' hyy' = c₃.get y y' hyy'_G₃ := hc_G₃ hyy'_G₃
  have hc_zz' : c.get z z' hzz' = c₃.get z z' hzz'_G₃ := hc_G₃ hzz'_G₃

  have c_mem_Ew : ∀ {a : V}, ¬ A a → (ha : G.Adj a w') → c.get a w' ha ∈ mkE w w' := by
    intro a hna ha
    have ha₃ := adj_G₃_of_notA ha.symm (Or.inl hnA_w')
    rw [c_get_comm c ha, c_get_eq_of_sym2 c ha.symm (hG₃_le ha₃) rfl, hc_G₃ ha₃]
    exact mem_mkE (fun h => hna (Or.inl h)) ha₃
  have c_mem_Ex : ∀ {a : V}, ¬ A a → (ha : G.Adj a x') → c.get a x' ha ∈ mkE x x' := by
    intro a hna ha
    have ha₃ := adj_G₃_of_notA ha.symm (Or.inl hnA_x')
    rw [c_get_comm c ha, c_get_eq_of_sym2 c ha.symm (hG₃_le ha₃) rfl, hc_G₃ ha₃]
    exact mem_mkE (fun h => hna (Or.inr (Or.inl h))) ha₃
  have c_mem_Ey : ∀ {a : V}, ¬ A a → (ha : G.Adj a y') → c.get a y' ha ∈ mkE y y' := by
    intro a hna ha
    have ha₃ := adj_G₃_of_notA ha.symm (Or.inl hnA_y')
    rw [c_get_comm c ha, c_get_eq_of_sym2 c ha.symm (hG₃_le ha₃) rfl, hc_G₃ ha₃]
    exact mem_mkE (fun h => hna (Or.inr (Or.inr (Or.inl h)))) ha₃
  have c_mem_Ez : ∀ {a : V}, ¬ A a → (ha : G.Adj a z') → c.get a z' ha ∈ mkE z z' := by
    intro a hna ha
    have ha₃ := adj_G₃_of_notA ha.symm (Or.inl hnA_z')
    rw [c_get_comm c ha, c_get_eq_of_sym2 c ha.symm (hG₃_le ha₃) rfl, hc_G₃ ha₃]
    exact mem_mkE (fun h => hna (Or.inr (Or.inr (Or.inr h)))) ha₃

  have no_alt_exit : ∀ u₀ u₁ u₂ u₃ : V,
      [u₀, u₁, u₂, u₃].Nodup →
      (h01 : G.Adj u₀ u₁) → (h12 : G.Adj u₁ u₂) → (h23 : G.Adj u₂ u₃) →
      A u₀ → ¬ A u₁ →
      c.get u₀ u₁ h01 ≠ c.get u₂ u₃ h23 := by
    intro u₀ u₁ u₂ u₃ hnd4 h01 h12 h23 hA0 hnA1
    rcases nodup4_elim hnd4 with ⟨_, n02, n03, _, _, _⟩
    have hnA2 : ¬ A u₂ := by
      intro hA2
      rcases adj_A_notA hA0 hnA1 h01 with ⟨hu0, hu1⟩ | ⟨hu0, hu1⟩ | ⟨hu0, hu1⟩ | ⟨hu0, hu1⟩ <;>
        rcases adj_A_notA hA2 hnA1 h12.symm with ⟨hu2, hu1'⟩ | ⟨hu2, hu1'⟩ | ⟨hu2, hu1'⟩ | ⟨hu2, hu1'⟩
      · exact n02 (hu0.trans hu2.symm)
      · exact hw'_x' (hu1.symm.trans hu1')
      · exact hw'_y' (hu1.symm.trans hu1')
      · exact hw'_z' (hu1.symm.trans hu1')
      · exact hw'_x' (hu1'.symm.trans hu1)
      · exact n02 (hu0.trans hu2.symm)
      · exact hx'_y' (hu1.symm.trans hu1')
      · exact hx'_z' (hu1.symm.trans hu1')
      · exact hw'_y' (hu1'.symm.trans hu1)
      · exact hx'_y' (hu1'.symm.trans hu1)
      · exact n02 (hu0.trans hu2.symm)
      · exact hy'_z' (hu1.symm.trans hu1')
      · exact hw'_z' (hu1'.symm.trans hu1)
      · exact hx'_z' (hu1'.symm.trans hu1)
      · exact hy'_z' (hu1'.symm.trans hu1)
      · exact n02 (hu0.trans hu2.symm)
    have h12_init := adj_init_of_notA2 h12 hnA1 hnA2
    by_cases hA3 : A u₃
    · rcases adj_A_notA hA0 hnA1 h01 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        rcases adj_A_notA hA3 hnA2 h23.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd rfl n03
      · rw [c_get_eq_of_sym2 c h01 hww' rfl, hc_ww', c_get_comm c h23, c_get_eq_of_sym2 c h23.symm hxx' rfl, hc_xx']
        exact av_wx h12_init
      · rw [c_get_eq_of_sym2 c h01 hww' rfl, hc_ww', c_get_comm c h23, c_get_eq_of_sym2 c h23.symm hyy' rfl, hc_yy']
        exact av_wy h12_init
      · rw [c_get_eq_of_sym2 c h01 hww' rfl, hc_ww', c_get_comm c h23, c_get_eq_of_sym2 c h23.symm hzz' rfl, hc_zz']
        exact av_wz h12_init
      · rw [c_get_eq_of_sym2 c h01 hxx' rfl, hc_xx', c_get_comm c h23, c_get_eq_of_sym2 c h23.symm hww' rfl, hc_ww']
        exact (av_wx h12_init.symm).symm
      · exact absurd rfl n03
      · rw [c_get_eq_of_sym2 c h01 hxx' rfl, hc_xx', c_get_comm c h23, c_get_eq_of_sym2 c h23.symm hyy' rfl, hc_yy']
        exact av_xy h12_init
      · rw [c_get_eq_of_sym2 c h01 hxx' rfl, hc_xx', c_get_comm c h23, c_get_eq_of_sym2 c h23.symm hzz' rfl, hc_zz']
        exact av_xz h12_init
      · rw [c_get_eq_of_sym2 c h01 hyy' rfl, hc_yy', c_get_comm c h23, c_get_eq_of_sym2 c h23.symm hww' rfl, hc_ww']
        exact (av_wy h12_init.symm).symm
      · rw [c_get_eq_of_sym2 c h01 hyy' rfl, hc_yy', c_get_comm c h23, c_get_eq_of_sym2 c h23.symm hxx' rfl, hc_xx']
        exact (av_xy h12_init.symm).symm
      · exact absurd rfl n03
      · rw [c_get_eq_of_sym2 c h01 hyy' rfl, hc_yy', c_get_comm c h23, c_get_eq_of_sym2 c h23.symm hzz' rfl, hc_zz']
        exact av_yz h12_init
      · rw [c_get_eq_of_sym2 c h01 hzz' rfl, hc_zz', c_get_comm c h23, c_get_eq_of_sym2 c h23.symm hww' rfl, hc_ww']
        exact (av_wz h12_init.symm).symm
      · rw [c_get_eq_of_sym2 c h01 hzz' rfl, hc_zz', c_get_comm c h23, c_get_eq_of_sym2 c h23.symm hxx' rfl, hc_xx']
        exact (av_xz h12_init.symm).symm
      · rw [c_get_eq_of_sym2 c h01 hzz' rfl, hc_zz', c_get_comm c h23, c_get_eq_of_sym2 c h23.symm hyy' rfl, hc_yy']
        exact (av_yz h12_init.symm).symm
      · exact absurd rfl n03
    · have h23_init := adj_init_of_notA2 h23 hnA2 hA3
      have h23_G₃ := adj_G₃_of_notA h23 (Or.inl hnA2)
      rw [c_get_eq_of_sym2 c h23 (hG₃_le h23_G₃) rfl, hc_G₃ h23_G₃]
      rcases adj_A_notA hA0 hnA1 h01 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [c_get_eq_of_sym2 c h01 hww' rfl, hc_ww']; exact (av_w h12_init h23_init h23_G₃).symm
      · rw [c_get_eq_of_sym2 c h01 hxx' rfl, hc_xx']; exact (av_x h12_init h23_init h23_G₃).symm
      · rw [c_get_eq_of_sym2 c h01 hyy' rfl, hc_yy']; exact (av_y h12_init h23_init h23_G₃).symm
      · rw [c_get_eq_of_sym2 c h01 hzz' rfl, hc_zz']; exact (av_z h12_init h23_init h23_G₃).symm

  refine ⟨c, ?_, ?_, ?_⟩
  · -- 1. IsProperEdgeColoring c
    intro v a b hva hvb hab
    by_cases hv : A v
    · rcases hv with rfl | rfl | rfl | rfl
      · rcases (adj_w a).mp hva with rfl | rfl <;> rcases (adj_w b).mp hvb with rfl | rfl
        · exact absurd rfl hab
        · rw [c_get_eq_of_sym2 c hva hwx rfl, hc_wx, c_get_eq_of_sym2 c hvb hww' rfl, hc_ww']
          exact hcp_cs
        · rw [c_get_eq_of_sym2 c hva hww' rfl, hc_ww', c_get_eq_of_sym2 c hvb hwx rfl, hc_wx]
          exact hcp_cs.symm
        · exact absurd rfl hab
      · rcases (adj_x a).mp hva with rfl | rfl | rfl <;>
          rcases (adj_x b).mp hvb with rfl | rfl | rfl
        · exact absurd rfl hab
        · rw [c_get_comm c hva, c_get_eq_of_sym2 c hva.symm hwx rfl, hc_wx,
            c_get_eq_of_sym2 c hvb hxy rfl, hc_xy]
          exact hcp_cq
        · rw [c_get_comm c hva, c_get_eq_of_sym2 c hva.symm hwx rfl, hc_wx,
            c_get_eq_of_sym2 c hvb hxx' rfl, hc_xx']
          exact hcp_ct
        · rw [c_get_eq_of_sym2 c hva hxy rfl, hc_xy,
            c_get_comm c hvb, c_get_eq_of_sym2 c hvb.symm hwx rfl, hc_wx]
          exact hcp_cq.symm
        · exact absurd rfl hab
        · rw [c_get_eq_of_sym2 c hva hxy rfl, hc_xy,
            c_get_eq_of_sym2 c hvb hxx' rfl, hc_xx']
          exact hcq_ct
        · rw [c_get_eq_of_sym2 c hva hxx' rfl, hc_xx',
            c_get_comm c hvb, c_get_eq_of_sym2 c hvb.symm hwx rfl, hc_wx]
          exact hcp_ct.symm
        · rw [c_get_eq_of_sym2 c hva hxx' rfl, hc_xx',
            c_get_eq_of_sym2 c hvb hxy rfl, hc_xy]
          exact hcq_ct.symm
        · exact absurd rfl hab
      · rcases (adj_y a).mp hva with rfl | rfl | rfl <;>
          rcases (adj_y b).mp hvb with rfl | rfl | rfl
        · exact absurd rfl hab
        · rw [c_get_comm c hva, c_get_eq_of_sym2 c hva.symm hxy rfl, hc_xy,
            c_get_eq_of_sym2 c hvb hyz rfl, hc_yz]
          exact hcr_cq.symm
        · rw [c_get_comm c hva, c_get_eq_of_sym2 c hva.symm hxy rfl, hc_xy,
            c_get_eq_of_sym2 c hvb hyy' rfl, hc_yy']
          exact hcq_cu
        · rw [c_get_eq_of_sym2 c hva hyz rfl, hc_yz,
            c_get_comm c hvb, c_get_eq_of_sym2 c hvb.symm hxy rfl, hc_xy]
          exact hcr_cq
        · exact absurd rfl hab
        · rw [c_get_eq_of_sym2 c hva hyz rfl, hc_yz,
            c_get_eq_of_sym2 c hvb hyy' rfl, hc_yy']
          exact hcr_cu
        · rw [c_get_eq_of_sym2 c hva hyy' rfl, hc_yy',
            c_get_comm c hvb, c_get_eq_of_sym2 c hvb.symm hxy rfl, hc_xy]
          exact hcq_cu.symm
        · rw [c_get_eq_of_sym2 c hva hyy' rfl, hc_yy',
            c_get_eq_of_sym2 c hvb hyz rfl, hc_yz]
          exact hcr_cu.symm
        · exact absurd rfl hab
      · rcases (adj_z a).mp hva with rfl | rfl <;> rcases (adj_z b).mp hvb with rfl | rfl
        · exact absurd rfl hab
        · rw [c_get_comm c hva, c_get_eq_of_sym2 c hva.symm hyz rfl, hc_yz,
            c_get_eq_of_sym2 c hvb hzz' rfl, hc_zz']
          exact hcr_cv
        · rw [c_get_eq_of_sym2 c hva hzz' rfl, hc_zz',
            c_get_comm c hvb, c_get_eq_of_sym2 c hvb.symm hyz rfl, hc_yz]
          exact hcr_cv.symm
        · exact absurd rfl hab
    · have hva₃ := adj_G₃_of_notA hva (Or.inl hv)
      have hvb₃ := adj_G₃_of_notA hvb (Or.inl hv)
      rw [c_get_eq_of_sym2 c hva (hG₃_le hva₃) rfl, hc_G₃ hva₃,
        c_get_eq_of_sym2 c hvb (hG₃_le hvb₃) rfl, hc_G₃ hvb₃]
      exact hc₃.1 v a b hva₃ hvb₃ hab

  · -- 2. ¬ HasBicoloredPathFour c
    let IsBicP4 (v₀ v₁ v₂ v₃ v₄ : V) : Prop :=
      [v₀, v₁, v₂, v₃, v₄].Nodup ∧
      ∃ (h01 : G.Adj v₀ v₁) (h12 : G.Adj v₁ v₂) (h23 : G.Adj v₂ v₃) (h34 : G.Adj v₃ v₄),
        c.get v₀ v₁ h01 = c.get v₂ v₃ h23 ∧ c.get v₁ v₂ h12 = c.get v₃ v₄ h34
    have rev_P4 : ∀ {v₀ v₁ v₂ v₃ v₄ : V}, IsBicP4 v₀ v₁ v₂ v₃ v₄ → IsBicP4 v₄ v₃ v₂ v₁ v₀ := by
      rintro v₀ v₁ v₂ v₃ v₄ ⟨hnd5, h01, h12, h23, h34, eq1, eq2⟩
      refine ⟨nodup5_rev hnd5, h34.symm, h23.symm, h12.symm, h01.symm, ?_, ?_⟩
      · rw [c_get_symm c h34, c_get_symm c h12]; exact eq2.symm
      · rw [c_get_symm c h23, c_get_symm c h01]; exact eq1.symm

    have refute_FFTTF : ∀ {v₀ v₁ v₂ v₃ v₄ : V}, IsBicP4 v₀ v₁ v₂ v₃ v₄ →
        ¬ A v₀ → ¬ A v₁ → A v₂ → A v₃ → ¬ A v₄ → False := by
      rintro v₀ v₁ v₂ v₃ v₄ ⟨_, h01, h12, h23, h34, eq1, eq2⟩ hnA0 hnA1 hA2 hA3 hnA4
      rcases adj_A_A hA2 hA3 h23 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases adj_A_notA hA2 hnA1 h12.symm with ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
        swap; · exact hw_x h
        swap; · exact hw_y h
        swap; · exact hw_z h
        rcases adj_A_notA hA3 hnA4 h34 with ⟨h, _⟩ | ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩
        · exact hw_x h.symm
        · rw [c_get_comm c h12, c_get_eq_of_sym2 c h12.symm hww' rfl, hc_ww',
            c_get_eq_of_sym2 c h34 hxx' rfl, hc_xx'] at eq2
          rw [c_get_eq_of_sym2 c h23 hwx rfl, hc_wx] at eq1
          exact (h_cs_ct eq2).1 (eq1 ▸ c_mem_Ew hnA0 h01)
        · exact hx_y h
        · exact hx_z h
      · rcases adj_A_notA hA2 hnA1 h12.symm with ⟨h, _⟩ | ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩
        · exact hw_x h.symm
        · rcases adj_A_notA hA3 hnA4 h34 with ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
          · rw [c_get_comm c h12, c_get_eq_of_sym2 c h12.symm hxx' rfl, hc_xx',
              c_get_eq_of_sym2 c h34 hww' rfl, hc_ww'] at eq2
            rw [c_get_comm c h23, c_get_eq_of_sym2 c h23.symm hwx rfl, hc_wx] at eq1
            exact (h_cs_ct eq2.symm).2 (eq1 ▸ c_mem_Ex hnA0 h01)
          · exact hw_x h
          · exact hw_y h
          · exact hw_z h
        · exact hx_y h
        · exact hx_z h
      · rcases adj_A_notA hA2 hnA1 h12.symm with ⟨h, _⟩ | ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩
        · exact hw_x h.symm
        · rw [c_get_eq_of_sym2 c h23 hxy rfl, hc_xy] at eq1
          exact hcq_Ex (eq1 ▸ c_mem_Ex hnA0 h01)
        · exact hx_y h
        · exact hx_z h
      · rcases adj_A_notA hA2 hnA1 h12.symm with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, rfl⟩ | ⟨h, _⟩
        · exact hw_y h.symm
        · exact hx_y h.symm
        · rw [c_get_comm c h23, c_get_eq_of_sym2 c h23.symm hxy rfl, hc_xy] at eq1
          exact hcq_Ey (eq1 ▸ c_mem_Ey hnA0 h01)
        · exact hy_z h
      · rcases adj_A_notA hA2 hnA1 h12.symm with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, rfl⟩ | ⟨h, _⟩
        · exact hw_y h.symm
        · exact hx_y h.symm
        · rcases adj_A_notA hA3 hnA4 h34 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, rfl⟩
          · exact hw_z h.symm
          · exact hx_z h.symm
          · exact hy_z h.symm
          · rw [c_get_comm c h12, c_get_eq_of_sym2 c h12.symm hyy' rfl, hc_yy',
              c_get_eq_of_sym2 c h34 hzz' rfl, hc_zz'] at eq2
            rw [c_get_eq_of_sym2 c h23 hyz rfl, hc_yz] at eq1
            exact (h_cu_cv eq2).1 (eq1 ▸ c_mem_Ey hnA0 h01)
        · exact hy_z h
      · rcases adj_A_notA hA2 hnA1 h12.symm with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, rfl⟩
        · exact hw_z h.symm
        · exact hx_z h.symm
        · exact hy_z h.symm
        · rcases adj_A_notA hA3 hnA4 h34 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, rfl⟩ | ⟨h, _⟩
          · exact hw_y h.symm
          · exact hx_y h.symm
          · rw [c_get_comm c h12, c_get_eq_of_sym2 c h12.symm hzz' rfl, hc_zz',
              c_get_eq_of_sym2 c h34 hyy' rfl, hc_yy'] at eq2
            rw [c_get_comm c h23, c_get_eq_of_sym2 c h23.symm hyz rfl, hc_yz] at eq1
            exact (h_cu_cv eq2.symm).2 (eq1 ▸ c_mem_Ez hnA0 h01)
          · exact hy_z h

    have refute_FFTTT : ∀ {v₀ v₁ v₂ v₃ v₄ : V}, IsBicP4 v₀ v₁ v₂ v₃ v₄ →
        ¬ A v₀ → ¬ A v₁ → A v₂ → A v₃ → A v₄ → False := by
      rintro v₀ v₁ v₂ v₃ v₄ ⟨hnd5, h01, h12, h23, h34, eq1, eq2⟩ hnA0 hnA1 hA2 hA3 hA4
      rcases nodup5_elim hnd5 with ⟨_, _, _, _, _, _, _, _, n24, _⟩
      rcases path2_A hA2 hA3 hA4 n24 h23 h34 with
          ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · rcases adj_A_notA hA2 hnA1 h12.symm with ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
        · rw [c_get_comm c h12, c_get_eq_of_sym2 c h12.symm hww' rfl, hc_ww',
            c_get_eq_of_sym2 c h34 hxy rfl, hc_xy] at eq2
          rw [c_get_eq_of_sym2 c h23 hwx rfl, hc_wx] at eq1
          exact (h_cs_cq eq2).1 (eq1 ▸ c_mem_Ew hnA0 h01)
        · exact hw_x h
        · exact hw_y h
        · exact hw_z h
      · rcases adj_A_notA hA2 hnA1 h12.symm with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, rfl⟩ | ⟨h, _⟩
        · exact hw_y h.symm
        · exact hx_y h.symm
        · rw [c_get_comm c h23, c_get_eq_of_sym2 c h23.symm hxy rfl, hc_xy] at eq1
          exact hcq_Ey (eq1 ▸ c_mem_Ey hnA0 h01)
        · exact hy_z h
      · rcases adj_A_notA hA2 hnA1 h12.symm with ⟨h, _⟩ | ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩
        · exact hw_x h.symm
        · rw [c_get_eq_of_sym2 c h23 hxy rfl, hc_xy] at eq1
          exact hcq_Ex (eq1 ▸ c_mem_Ex hnA0 h01)
        · exact hx_y h
        · exact hx_z h
      · rcases adj_A_notA hA2 hnA1 h12.symm with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, rfl⟩
        · exact hw_z h.symm
        · exact hx_z h.symm
        · exact hy_z h.symm
        · rw [c_get_comm c h12, c_get_eq_of_sym2 c h12.symm hzz' rfl, hc_zz',
            c_get_comm c h34, c_get_eq_of_sym2 c h34.symm hxy rfl, hc_xy] at eq2
          rw [c_get_comm c h23, c_get_eq_of_sym2 c h23.symm hyz rfl, hc_yz] at eq1
          exact (h_cv_cq eq2).1 (eq1 ▸ c_mem_Ez hnA0 h01)

    have refute_FTTTF : ∀ {v₀ v₁ v₂ v₃ v₄ : V}, IsBicP4 v₀ v₁ v₂ v₃ v₄ →
        ¬ A v₀ → A v₁ → A v₂ → A v₃ → ¬ A v₄ → False := by
      rintro v₀ v₁ v₂ v₃ v₄ ⟨hnd5, h01, h12, h23, h34, eq1, eq2⟩ hnA0 hA1 hA2 hA3 hnA4
      rcases nodup5_elim hnd5 with ⟨_, _, _, _, _, n13, _, _, _, _⟩
      rcases path2_A hA1 hA2 hA3 n13 h12 h23 with
          ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · rcases adj_A_notA hA1 hnA0 h01.symm with ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
        swap; · exact hw_x h
        swap; · exact hw_y h
        swap; · exact hw_z h
        rcases adj_A_notA hA3 hnA4 h34 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, rfl⟩ | ⟨h, _⟩
        · exact hw_y h.symm
        · exact hx_y h.symm
        · rw [c_get_comm c h01, c_get_eq_of_sym2 c h01.symm hww' rfl, hc_ww',
            c_get_eq_of_sym2 c h23 hxy rfl, hc_xy] at eq1
          rw [c_get_eq_of_sym2 c h12 hwx rfl, hc_wx,
            c_get_eq_of_sym2 c h34 hyy' rfl, hc_yy'] at eq2
          exact (h_cs_cq eq1).2.1 eq2
        · exact hy_z h
      · rcases adj_A_notA hA1 hnA0 h01.symm with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, rfl⟩ | ⟨h, _⟩
        · exact hw_y h.symm
        · exact hx_y h.symm
        · rcases adj_A_notA hA3 hnA4 h34 with ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
          · rw [c_get_comm c h12, c_get_eq_of_sym2 c h12.symm hxy rfl, hc_xy,
              c_get_eq_of_sym2 c h34 hww' rfl, hc_ww'] at eq2
            rw [c_get_comm c h01, c_get_eq_of_sym2 c h01.symm hyy' rfl, hc_yy',
              c_get_comm c h23, c_get_eq_of_sym2 c h23.symm hwx rfl, hc_wx] at eq1
            exact (h_cs_cq eq2.symm).2.1 eq1.symm
          · exact hw_x h
          · exact hw_y h
          · exact hw_z h
        · exact hy_z h
      · rcases adj_A_notA hA1 hnA0 h01.symm with ⟨h, _⟩ | ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩
        · exact hw_x h.symm
        · rcases adj_A_notA hA3 hnA4 h34 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, rfl⟩
          · exact hw_z h.symm
          · exact hx_z h.symm
          · exact hy_z h.symm
          · rw [c_get_eq_of_sym2 c h12 hxy rfl, hc_xy,
              c_get_eq_of_sym2 c h34 hzz' rfl, hc_zz'] at eq2
            rw [c_get_comm c h01, c_get_eq_of_sym2 c h01.symm hxx' rfl, hc_xx',
              c_get_eq_of_sym2 c h23 hyz rfl, hc_yz] at eq1
            exact (h_cv_cq eq2.symm).2.1 eq1.symm
        · exact hx_y h
        · exact hx_z h
      · rcases adj_A_notA hA1 hnA0 h01.symm with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, rfl⟩
        · exact hw_z h.symm
        · exact hx_z h.symm
        · exact hy_z h.symm
        · rcases adj_A_notA hA3 hnA4 h34 with ⟨h, _⟩ | ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩
          · exact hw_x h.symm
          · rw [c_get_comm c h01, c_get_eq_of_sym2 c h01.symm hzz' rfl, hc_zz',
              c_get_comm c h23, c_get_eq_of_sym2 c h23.symm hxy rfl, hc_xy] at eq1
            rw [c_get_comm c h12, c_get_eq_of_sym2 c h12.symm hyz rfl, hc_yz,
              c_get_eq_of_sym2 c h34 hxx' rfl, hc_xx'] at eq2
            exact (h_cv_cq eq1).2.1 eq2
          · exact hx_y h
          · exact hx_z h

    have refute_FTTTT : ∀ {v₀ v₁ v₂ v₃ v₄ : V}, IsBicP4 v₀ v₁ v₂ v₃ v₄ →
        ¬ A v₀ → A v₁ → A v₂ → A v₃ → A v₄ → False := by
      rintro v₀ v₁ v₂ v₃ v₄ ⟨hnd5, h01, h12, h23, h34, eq1, eq2⟩ hnA0 hA1 hA2 hA3 hA4
      have hnd14 : [v₁, v₂, v₃, v₄].Nodup := (List.nodup_cons.mp hnd5).2
      rcases path3_A hA1 hA2 hA3 hA4 hnd14 h12 h23 h34 with
          ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
      · rcases adj_A_notA hA1 hnA0 h01.symm with ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
        · rw [c_get_comm c h01, c_get_eq_of_sym2 c h01.symm hww' rfl, hc_ww',
            c_get_eq_of_sym2 c h23 hxy rfl, hc_xy] at eq1
          rw [c_get_eq_of_sym2 c h12 hwx rfl, hc_wx,
            c_get_eq_of_sym2 c h34 hyz rfl, hc_yz] at eq2
          exact (h_cs_cq eq1).2.2 eq2
        · exact hw_x h
        · exact hw_y h
        · exact hw_z h
      · rcases adj_A_notA hA1 hnA0 h01.symm with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, rfl⟩
        · exact hw_z h.symm
        · exact hx_z h.symm
        · exact hy_z h.symm
        · rw [c_get_comm c h01, c_get_eq_of_sym2 c h01.symm hzz' rfl, hc_zz',
            c_get_comm c h23, c_get_eq_of_sym2 c h23.symm hxy rfl, hc_xy] at eq1
          rw [c_get_comm c h12, c_get_eq_of_sym2 c h12.symm hyz rfl, hc_yz,
            c_get_comm c h34, c_get_eq_of_sym2 c h34.symm hwx rfl, hc_wx] at eq2
          exact (h_cv_cq eq1).2.2 eq2

    rintro ⟨v₀, v₁, v₂, v₃, v₄, hnd5, h01, h12, h23, h34, eq1, eq2⟩
    have hP4 : IsBicP4 v₀ v₁ v₂ v₃ v₄ := ⟨hnd5, h01, h12, h23, h34, eq1, eq2⟩
    have no_TF_01 : ¬ (A v₀ ∧ ¬ A v₁) := fun ⟨h0, hn1⟩ =>
      no_alt_exit v₀ v₁ v₂ v₃ (nodup5_init hnd5) h01 h12 h23 h0 hn1 eq1
    have no_TF_12 : ¬ (A v₁ ∧ ¬ A v₂) := fun ⟨h1, hn2⟩ =>
      no_alt_exit v₁ v₂ v₃ v₄ ((List.nodup_cons.mp hnd5).2) h12 h23 h34 h1 hn2 eq2
    have no_FT_23 : ¬ (¬ A v₂ ∧ A v₃) := by
      intro ⟨hn2, h3⟩
      rcases rev_P4 hP4 with ⟨hnd5r, h34r, h23r, h12r, h01r, _, eq2r⟩
      exact no_alt_exit v₃ v₂ v₁ v₀ ((List.nodup_cons.mp hnd5r).2) h23r h12r h01r h3 hn2 eq2r
    have no_FT_34 : ¬ (¬ A v₃ ∧ A v₄) := by
      intro ⟨hn3, h4⟩
      rcases rev_P4 hP4 with ⟨hnd5r, h34r, h23r, h12r, _, eq1r, _⟩
      exact no_alt_exit v₄ v₃ v₂ v₁ (nodup5_init hnd5r) h34r h23r h12r h4 hn3 eq1r

    by_cases hA2 : A v₂
    · by_cases hA1 : A v₁
      · by_cases hA0 : A v₀
        · by_cases hA3 : A v₃
          · by_cases hA4 : A v₄
            · exact not_nodup_five_of_four hnd5 hA0 hA1 hA2 hA3 hA4
            · exact refute_FTTTT (rev_P4 hP4) hA4 hA3 hA2 hA1 hA0
          · have hnA4 : ¬ A v₄ := fun h4 => no_FT_34 ⟨hA3, h4⟩
            exact refute_FFTTT (rev_P4 hP4) hnA4 hA3 hA2 hA1 hA0
        · by_cases hA3 : A v₃
          · by_cases hA4 : A v₄
            · exact refute_FTTTT hP4 hA0 hA1 hA2 hA3 hA4
            · exact refute_FTTTF hP4 hA0 hA1 hA2 hA3 hA4
          · have hnA4 : ¬ A v₄ := fun h4 => no_FT_34 ⟨hA3, h4⟩
            exact refute_FFTTF (rev_P4 hP4) hnA4 hA3 hA2 hA1 hA0
      · have hnA0 : ¬ A v₀ := fun h0 => no_TF_01 ⟨h0, hA1⟩
        by_cases hA3 : A v₃
        · by_cases hA4 : A v₄
          · exact refute_FFTTT hP4 hnA0 hA1 hA2 hA3 hA4
          · exact refute_FFTTF hP4 hnA0 hA1 hA2 hA3 hA4
        · have hnA4 : ¬ A v₄ := fun h4 => no_FT_34 ⟨hA3, h4⟩
          have g01 := adj_G₃_of_notA h01 (Or.inl hnA0)
          have g12 := adj_G₃_of_notA h12 (Or.inl hA1)
          have g23 := adj_G₃_of_notA h23 (Or.inr hA3)
          have g34 := adj_G₃_of_notA h34 (Or.inl hA3)
          rw [c_get_eq_of_sym2 c h01 (hG₃_le g01) rfl, hc_G₃ g01,
            c_get_eq_of_sym2 c h23 (hG₃_le g23) rfl, hc_G₃ g23] at eq1
          rw [c_get_eq_of_sym2 c h12 (hG₃_le g12) rfl, hc_G₃ g12,
            c_get_eq_of_sym2 c h34 (hG₃_le g34) rfl, hc_G₃ g34] at eq2
          exact hc₃.2.1 ⟨v₀, v₁, v₂, v₃, v₄, hnd5, g01, g12, g23, g34, eq1, eq2⟩
    · have hnA1 : ¬ A v₁ := fun h1 => no_TF_12 ⟨h1, hA2⟩
      have hnA0 : ¬ A v₀ := fun h0 => no_TF_01 ⟨h0, hnA1⟩
      have hnA3 : ¬ A v₃ := fun h3 => no_FT_23 ⟨hA2, h3⟩
      have hnA4 : ¬ A v₄ := fun h4 => no_FT_34 ⟨hnA3, h4⟩
      have g01 := adj_G₃_of_notA h01 (Or.inl hnA0)
      have g12 := adj_G₃_of_notA h12 (Or.inl hnA1)
      have g23 := adj_G₃_of_notA h23 (Or.inl hA2)
      have g34 := adj_G₃_of_notA h34 (Or.inl hnA3)
      rw [c_get_eq_of_sym2 c h01 (hG₃_le g01) rfl, hc_G₃ g01,
        c_get_eq_of_sym2 c h23 (hG₃_le g23) rfl, hc_G₃ g23] at eq1
      rw [c_get_eq_of_sym2 c h12 (hG₃_le g12) rfl, hc_G₃ g12,
        c_get_eq_of_sym2 c h34 (hG₃_le g34) rfl, hc_G₃ g34] at eq2
      exact hc₃.2.1 ⟨v₀, v₁, v₂, v₃, v₄, hnd5, g01, g12, g23, g34, eq1, eq2⟩

  · -- 3. ¬ HasBicoloredCycleFour c
    rintro ⟨v₀, v₁, v₂, v₃, hnd4, h01, h12, h23, h30, eq1, eq2⟩
    have hrot1 : [v₁, v₂, v₃, v₀].Nodup := nodup4_rot hnd4
    have hrot2 : [v₂, v₃, v₀, v₁].Nodup := nodup4_rot hrot1
    have hrot3 : [v₃, v₀, v₁, v₂].Nodup := nodup4_rot hrot2
    by_cases h0 : A v₀
    · by_cases h1 : A v₁
      · by_cases h2 : A v₂
        · by_cases h3 : A v₃
          · have w_in_A_adj : ∀ {u a b : V}, u = w → A a → A b → a ≠ b →
                G.Adj u a → G.Adj u b → False := by
              intro u a b hu ha hb hab hua hub
              rcases adj_A_A (hu ▸ Or.inl rfl) ha hua with
                  ⟨_, ha_x⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
              swap; · exact hw_x (hu.symm.trans h)
              swap; · exact hw_x (hu.symm.trans h)
              swap; · exact hw_y (hu.symm.trans h)
              swap; · exact hw_y (hu.symm.trans h)
              swap; · exact hw_z (hu.symm.trans h)
              rcases adj_A_A (hu ▸ Or.inl rfl) hb hub with
                  ⟨_, hb_x⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
              · exact hab (ha_x.trans hb_x.symm)
              · exact hw_x (hu.symm.trans h)
              · exact hw_x (hu.symm.trans h)
              · exact hw_y (hu.symm.trans h)
              · exact hw_y (hu.symm.trans h)
              · exact hw_z (hu.symm.trans h)
            rcases nodup4_elim hnd4 with ⟨_, n02, _, _, n13, _⟩
            by_cases hw0 : v₀ = w
            · exact w_in_A_adj hw0 h1 h3 n13 h01 h30.symm
            · by_cases hw1 : v₁ = w
              · exact w_in_A_adj hw1 h0 h2 n02 h01.symm h12
              · by_cases hw2 : v₂ = w
                · exact w_in_A_adj hw2 h1 h3 n13 h12.symm h23
                · by_cases hw3 : v₃ = w
                  · exact w_in_A_adj hw3 h0 h2 n02 h30 h23.symm
                  · exact not_nodup_four_of_three hnd4
                      (h0.resolve_left hw0) (h1.resolve_left hw1)
                      (h2.resolve_left hw2) (h3.resolve_left hw3)
          · exact no_alt_exit v₂ v₃ v₀ v₁ hrot2 h23 h30 h01 h2 h3 eq1.symm
        · exact no_alt_exit v₁ v₂ v₃ v₀ hrot1 h12 h23 h30 h1 h2 eq2
      · exact no_alt_exit v₀ v₁ v₂ v₃ hnd4 h01 h12 h23 h0 h1 eq1
    · by_cases h3 : A v₃
      · exact no_alt_exit v₃ v₀ v₁ v₂ hrot3 h30 h01 h12 h3 h0 eq2.symm
      · by_cases h2 : A v₂
        · exact no_alt_exit v₂ v₃ v₀ v₁ hrot2 h23 h30 h01 h2 h3 eq1.symm
        · by_cases h1 : A v₁
          · exact no_alt_exit v₁ v₂ v₃ v₀ hrot1 h12 h23 h30 h1 h2 eq2
          · have g01 := adj_G₃_of_notA h01 (Or.inl h0)
            have g12 := adj_G₃_of_notA h12 (Or.inl h1)
            have g23 := adj_G₃_of_notA h23 (Or.inl h2)
            have g30 := adj_G₃_of_notA h30 (Or.inl h3)
            rw [c_get_eq_of_sym2 c h01 (hG₃_le g01) rfl, hc_G₃ g01,
              c_get_eq_of_sym2 c h23 (hG₃_le g23) rfl, hc_G₃ g23] at eq1
            rw [c_get_eq_of_sym2 c h12 (hG₃_le g12) rfl, hc_G₃ g12,
              c_get_eq_of_sym2 c h30 (hG₃_le g30) rfl, hc_G₃ g30] at eq2
            exact hc₃.2.2 ⟨v₀, v₁, v₂, v₃, hnd4, g01, g12, g23, g30, eq1, eq2⟩

/-- Corollary assuming `HasStarEdgeColoring (G.deleteEdges {s(w, x), s(x, y), s(y, z)}) 7`. -/
theorem solution {V : Type u} [Fintype V]
    {G : SimpleGraph V} (hsub : IsSubcubic G) (w x y z w' x' y' z' : V)
    (hnd : [w, x, y, z, w', x', y', z'].Nodup)
    (hwx : G.Adj w x) (hxy : G.Adj x y) (hyz : G.Adj y z)
    (hww' : G.Adj w w') (hxx' : G.Adj x x') (hyy' : G.Adj y y') (hzz' : G.Adj z z')
    (hw2 : (G.neighborSet w).encard ≤ 2) (hz2 : (G.neighborSet z).encard ≤ 2)
    (hc' : HasStarEdgeColoring (G.deleteEdges {s(w, x), s(x, y), s(y, z)}) 7) :
    HasStarEdgeColoring G 7 := by
  rcases hc' with ⟨c₃, hc₃⟩
  have hle : G.deleteEdges {s(w, x), s(x, y), s(y, z), s(w, w'), s(x, x'), s(y, y'), s(z, z')} ≤
      G.deleteEdges {s(w, x), s(x, y), s(y, z)} := by
    intro a b hab
    rcases SimpleGraph.deleteEdges_adj.mp hab with ⟨habG, hnot⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hnot
    refine SimpleGraph.deleteEdges_adj.mpr ⟨habG, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hnot.1, hnot.2.1, hnot.2.2.1⟩
  exact hasStarEdgeColoring_of_deg2_path4_distinct hsub w x y z w' x' y' z' hnd
    hwx hxy hyz hww' hxx' hyy' hzz' hw2 hz2 ⟨restrictColoring hle c₃, isStarEdgeColoring_mono hle hc₃⟩
